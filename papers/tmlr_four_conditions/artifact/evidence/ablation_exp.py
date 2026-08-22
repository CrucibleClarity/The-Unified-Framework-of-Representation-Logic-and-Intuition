"""ablation_exp.py — decoupling 三子句消融 + 多配置鲁棒性 (TMLR 版)

输出指标 (每 run):
  curve: group, cond, seed, dim, layers, epoch, pt_ood, seq_ood
          pt_ood = per-token OOD 重建正确率 (逐 token argmax 对齐目标)
          seq_ood = 序列级 (全对) 正确率
  summary: group, cond, seed, dim, layers, epochs,
           pt_ood_final, peak_epoch, peak_pt_ood, hit_one, norm_pt
          peak_epoch = 第一个 pt_ood==1.0 的 epoch; 若未达 1,
                       则 = 第一个达到 max(pt_ood) 的 epoch
          norm_pt   = pt_ood_final / peak_epoch (per-token ood 除以
                       达到 ood=1 的 epochs; 未达 1 则除以达到最大
                       ood 的 epochs)

消融组 (decoupling D = exclusion + cancellation + layering):
  baseline      纯净 succ_a 训练 → OOD succ_a        (对照 E12 ①a)
  no_decl       纯净 succ_a → OOD succ_b (无声明)    (对照 E12 ①b)
  decl_full     succ_a + 等价/锚定错题 → OOD succ_b   (对照 E12 ②)
  excl_pollute  违反 exclusion: 训练样本混入噪声符号 (10%/30%)
  canc_1side    违反 cancellation: 等价样本单向呈现 (succ_a 恒在左)
  layer_dual    违反 layering: 同一符号双角色 (op + bracket)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import torch

import importlib
sm = importlib.import_module('succ矩阵实验')
sm_init, gen_arith, gen_equiv, gen_anchor_wrong = (sm.init, sm.gen_arith,
    sm.gen_equiv, sm.gen_anchor_wrong)
gen_ood, op_sample, chain, eq_prop = (sm.gen_ood, sm.op_sample,
    sm.chain, sm.eq_prop)
ADD, MUL, TOK, api = sm.ADD, sm.MUL, sm.TOK, sm.api
from lab.synth_core import inject_dual_tokens
from train.data import collate, rev_vocab
from train import train_seq

OUT_CURVE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "结果", "ablation_curve.tsv")
OUT_SUM = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "结果", "ablation_summary.tsv")

NOISE = {}   # eid 缓存


def init():
    sm_init()
    # exclusion: 噪声符号 (无定义目标的无关材料)
    inject_dual_tokens({
        "noise_x": {"form": "axiomatic", "arrange": "atom", "references": []},
        "duo": {"form": "explicit", "arrange": "application",
                "rules": [{"term": ["D:194"]}], "references": ["D:194"]},
    })
    NOISE["noise_x"] = api.eid_by_name("noise_x")
    NOISE["duo"] = api.eid_by_name("duo")


# ---------- per-token 评估 ----------

def eval_pt_seq(model, probes):
    """返回 (per_token_ood, seq_ood): 逐 token 重建正确率 + 全对序列比例."""
    rv = rev_vocab()
    batch = collate(probes, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v)
             for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    n_tok = n_ok = n_seq = n_seq_ok = 0
    for i, s in enumerate(probes):
        L = batch["inputs"].shape[1] - batch["mask"][i].sum().item()
        pred = [rv[p] for p in logits[i, :L].argmax(dim=1).tolist()]
        n_ok += sum(1 for p, t in zip(pred, s["seq"]) if p == t)
        n_tok += L
        n_seq += 1
        n_seq_ok += 1 if all(p == t for p, t in zip(pred, s["seq"])) else 0
    return n_ok / max(n_tok, 1), n_seq_ok / max(n_seq, 1)


# ---------- 消融数据生成 ----------

def pollute(samples, rate):
    """exclusion 违反: 在样本序列中随机插入噪声符号 (rate = 每序列比例)."""
    import random
    rng = random.Random(12345)
    out = []
    for s in samples:
        seq = list(s["seq"])
        k = max(1, int(len(seq) * rate))
        for _ in range(k):
            seq.insert(rng.randint(0, len(seq)), NOISE["noise_x"])
        ns = dict(s)
        ns["seq"] = seq
        out.append(ns)
    return out


def one_side_equiv(succ1, succ2, hi=9):
    """cancellation 违反: 等价样本只以 succ1 在左呈现 (单向)."""
    out = []
    for n in range(hi + 1):
        prop = eq_prop(chain(succ1, "basepoint", n),
                       chain(succ2, "basepoint", n))
        out.append(make_judged(prop, True))
    return out


def make_judged(prop, truth):
    from lab.judge import judge_sequence
    from gen_all_ops import make_sample
    return make_sample(judge_sequence(prop, truth), truth, 1)


def dual_role_arith(succ, bp, hi_add=9):
    """layering 违反: duo 同时充当 op (加) 和 bracket (包裹)."""
    out = []
    for m in range(hi_add + 1):
        for n in range(hi_add + 1):
            k = m + n
            lhs = api.assemble_seq(NOISE["duo"], [chain(succ, bp, m),
                                                  chain(succ, bp, n)])
            expr = api.assemble_seq(NOISE["duo"], [lhs])   # 同一符号再当 bracket
            prop = eq_prop(expr, chain(succ, bp, k))
            out.append(make_judged(prop, True))
            out.append(make_judged(prop, False) if False else
                       make_judged(eq_prop(expr, chain(succ, bp, k + 1)), False))
    return out


# ---------- 训练 + 曲线 ----------

def run_curve(group, cond, tr, od, seed, dim, layers, epochs):
    curve = []
    def fn(model):
        pt, seq = eval_pt_seq(model, od)
        curve.append((len(curve) + 1, pt, seq))
        return pt
    res = train_seq(tr, epochs=epochs, dim=dim, num_layers=layers,
                    seed=seed, epoch_eval_fn=fn)
    pt_final, seq_final = eval_pt_seq(res["model"], od)
    return curve, pt_final, seq_final


def summarize(group, cond, seed, dim, layers, epochs, curve, pt_final, seq_final):
    # peak_epoch: 第一个 pt_ood==1.0; 否则第一个达到 max 的 epoch
    peak_epoch = None
    peak_pt = 0.0
    hit_one = False
    for ep, pt, seq in curve:
        if pt >= 1.0 and not hit_one:
            peak_epoch, peak_pt, hit_one = ep, pt, True
            break
    if not hit_one:
        for ep, pt, seq in curve:
            if pt > peak_pt:
                peak_pt, peak_epoch = pt, ep
        if peak_epoch is None and curve:
            peak_epoch, peak_pt = curve[-1][0], curve[-1][1]
    norm_pt = pt_final / peak_epoch if peak_epoch else 0.0
    return dict(group=group, cond=cond, seed=seed, dim=dim, layers=layers,
                epochs=epochs, pt_ood_final=round(pt_final, 4),
                peak_epoch=peak_epoch, peak_pt_ood=round(peak_pt, 4),
                hit_one=int(hit_one), norm_pt=round(norm_pt, 4),
                seq_ood_final=round(seq_final, 4))


def main():
    os.makedirs("results", exist_ok=True)
    init()
    with open(OUT_CURVE, "w") as fc, open(OUT_SUM, "w") as fs:
        fc.write("group\tcond\tseed\tdim\tlayers\tepoch\tpt_ood\tseq_ood\n")
        fs.write("group\tcond\tseed\tdim\tlayers\tepochs\tpt_ood_final\t"
                 "peak_epoch\tpeak_pt_ood\thit_one\tnorm_pt\tseq_ood_final\n")

        def go(group, cond, tr, od, dim=64, layers=2, epochs=60, n_seed=3):
            for seed in range(n_seed):
                curve, pt_f, seq_f = run_curve(group, cond, tr, od, seed,
                                               dim, layers, epochs)
                for ep, pt, seq in curve:
                    fc.write(f"{group}\t{cond}\t{seed}\t{dim}\t{layers}\t"
                             f"{ep}\t{pt:.4f}\t{seq:.4f}\n")
                r = summarize(group, cond, seed, dim, layers, epochs,
                              curve, pt_f, seq_f)
                fs.write("\t".join(str(r[k]) for k in
                                   ("group", "cond", "seed", "dim", "layers",
                                    "epochs", "pt_ood_final", "peak_epoch",
                                    "peak_pt_ood", "hit_one", "norm_pt",
                                    "seq_ood_final")) + "\n")
                fs.flush(); fc.flush()
                print(f"[{group}/{cond}] seed={seed} dim={dim} layers={layers} "
                      f"pt_final={pt_f:.3f} seq_final={seq_f:.3f} "
                      f"peak_epoch={r['peak_epoch']} hit_one={r['hit_one']}",
                      flush=True)

        # --- 主配置 (dim=64, layers=2, epochs=60, 3 seeds) ---
        ood_a = gen_ood("succ_a", "basepoint")
        ood_b = gen_ood("succ_b", "basepoint")
        tr_a = gen_arith("succ_a", "basepoint")

        go("main", "baseline", tr_a, ood_a)                       # D 全满足
        go("main", "no_decl", tr_a, ood_b)                        # 无声明
        tr_full = tr_a + gen_equiv("succ_a", "succ_b") \
                  + gen_anchor_wrong("succ_a") + gen_anchor_wrong("succ_b")
        go("main", "decl_full", tr_full, ood_b)                   # 声明齐全
        # exclusion 违反: 污染 10% / 30%
        go("main", "excl_pollute10", pollute(tr_a, 0.10), ood_a)
        go("main", "excl_pollute30", pollute(tr_a, 0.30), ood_a)
        # cancellation 违反: 单向等价
        tr_1side = tr_a + one_side_equiv("succ_a", "succ_b") \
                   + gen_anchor_wrong("succ_a")
        go("main", "canc_1side", tr_1side, ood_b)
        # layering 违反: 双角色符号
        tr_dual = dual_role_arith("succ_a", "basepoint")
        go("main", "layer_dual", tr_dual, ood_a, n_seed=3)

        # --- 鲁棒性配置 (2 seeds) ---
        for dim, layers in ((128, 2), (64, 4), (128, 4)):
            go("robust", "baseline", tr_a, ood_a, dim=dim, layers=layers, n_seed=2)
            go("robust", "decl_full", tr_full, ood_b, dim=dim, layers=layers, n_seed=2)
            go("robust", "excl_pollute30", pollute(tr_a, 0.30), ood_a,
               dim=dim, layers=layers, n_seed=2)

    print("== 完成 ==", flush=True)


if __name__ == "__main__":
    main()
