"""E15严格实验.py — E14 的严格实验 (用户指令 2026-08-16: 继续做严格实验)

E14 结论: 对称轴 (中心) 不是锚 — 中点运算 (链长算术) 可外推。诚实边界:
② 组 OOD 部分 a,b 值训练过 (组合外推)。严格版补:

  ① 完全零样本中心漂移: 训 a,b ∈ [0,4] (中心 ≤4) → OOD a,b ∈ [5,9]
     (中心 5..9) — 输入链长全部未训练 (零样本 + 中心漂移同时)
  ② 跨表示剥离 (0 对照, I7ag 两极纪律): 训链长表示 → OOD 位置-值记法
     (numeral_of) — 期望 0 崩 (直觉路径 = 表示绑定)
  ③ 跨表示桥接: 训链长 + 等价对比题 (链长 = 位置-值) → OOD 位置-值
     — 期望 32/32 (0→1, 等价声明桥接跨表示)
  ④ 对称对完全零样本: 训中心 ≤3, 臂 d ≤2 → OOD 中心 4..6, d ∈ {3,4}
     — 中心与臂长全新
  ⑤ token 级报告: ① 与 ② 的位置正确率 (崩点形态 = 机制指纹)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import numeral_of, inject_dual_tokens
import torch
from train.data import collate, rev_vocab
from train import train_seq

MID = None


def init():
    global MID
    MID = api.eid_by_name("midpoint")


def chain_len(n):
    succ = api.eid_by_name("succ")
    bp = api.eid_by_name("basepoint")
    return [succ] * n + [bp]


def chain_pos(n):
    """位置-值记法 (numeral 结构: base/cardinality/digit)."""
    return numeral_of(n)


def op_sample(ch, m, n, k, truth):
    expr = api.assemble_seq(MID, [ch(m), ch(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, ch(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_arith(ch, lo=0, hi=8):
    """全枚举 a,b ∈ [lo,hi], a+b 偶: 真 (中点) + 假 (中点+1)."""
    out = []
    for a in range(lo, hi + 1):
        for b in range(lo, hi + 1):
            if (a + b) % 2:
                continue
            k = (a + b) // 2
            out.append(op_sample(ch, a, b, k, True))
            out.append(op_sample(ch, a, b, k + 1, False))
    return out


def gen_equiv(ch1, ch2, hi=4):
    """等价对比题: ch1(n) = ch2(n) (跨表示等价声明)."""
    out = []
    for n in range(hi + 1):
        prop = api.assemble_seq(api.role_token("equals"), [ch1(n), ch2(n)])
        out.append(make_sample(judge_sequence(prop, True), True, 1))
    return out


def gen_sym_pair_train(c_hi=3, d_hi=2):
    """对称对还原训练: {c−d, c+d} → c, 中心 ≤ c_hi, 臂 ≤ d_hi."""
    out = []
    for c in range(c_hi + 1):
        for d in range(1, d_hi + 1):
            a, b = c - d, c + d
            if a < 0:
                continue
            out.append(op_sample(chain_len, a, b, c, True))
            out.append(op_sample(chain_len, a, b, c + 1, False))
    return out


def gen_sym_pair_ood(c_lo=4, c_hi=6, d_lo=3, d_hi=4):
    """对称对还原 OOD: 中心 4..6, 臂 3..4 — 中心与臂长全新."""
    out = []
    for c in range(c_lo, c_hi + 1):
        for d in range(d_lo, d_hi + 1):
            a, b = c - d, c + d
            if a < 0:
                continue
            out.append(op_sample(chain_len, a, b, c, True))
            out.append(op_sample(chain_len, a, b, c + 1, False))
    return out


def evaluate_tok(model, probes, tag):
    """token 级报告: 样本全对数 + token 对/总数 + 位置正确率 (崩点定位)."""
    rv = rev_vocab()
    batch = collate(probes, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v) for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    L = batch["inputs"].shape[1]
    pos_ok = [0] * L
    pos_n = [0] * L
    ok = 0
    for i, s in enumerate(probes):
        Li = L - batch["mask"][i].sum().item()
        pred = [rv[p] for p in logits[i, :Li].argmax(dim=1).tolist()]
        if all(p == t for p, t in zip(pred, s["seq"])):
            ok += 1
        for j in range(Li):
            pos_n[j] += 1
            if pred[j] == s["seq"][j]:
                pos_ok[j] += 1
    t_ok = sum(pos_ok)
    t_n = sum(pos_n)
    print(f"{tag}: 样本 {ok}/{len(probes)} | token {t_ok}/{t_n} ({t_ok/t_n:.2f})", flush=True)
    print("   位置:", " ".join(f"{pos_ok[j]}/{pos_n[j]}" for j in range(L)), flush=True)


def evaluate(model, probes, tag):
    rv = rev_vocab()
    batch = collate(probes, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v) for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    ok = 0
    for i, s in enumerate(probes):
        Li = batch["inputs"].shape[1] - batch["mask"][i].sum().item()
        pred = [rv[p] for p in logits[i, :Li].argmax(dim=1).tolist()]
        if all(p == t for p, t in zip(pred, s["seq"])):
            ok += 1
    print(f"{tag}: {ok}/{len(probes)}", flush=True)


def run(label, tr, od, n_seed=3, tok=False):
    print(f"== {label}: 训练 {len(tr)} ==", flush=True)
    for seed in range(n_seed):
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        ev = evaluate_tok if tok else evaluate
        ev(res["model"], od, f"  seed={seed} 训练acc={res['valid_acc']:.3f}")


if __name__ == "__main__":
    init()
    # ① 完全零样本中心漂移: 训 a,b∈[0,4] → OOD a,b∈[5,9] (链长全未训练)
    run("① 完全零样本中心漂移 (训 [0,4] → OOD [5,9])", gen_arith(chain_len, 0, 4),
        gen_arith(chain_len, 5, 9), tok=True)
    # ② 跨表示剥离 (0 对照): 训链长 → OOD 位置-值
    run("② 跨表示剥离 (训链长 → OOD 位置-值)", gen_arith(chain_len, 0, 4),
        gen_arith(chain_pos, 0, 4), tok=True)
    # ③ 跨表示桥接: 训链长 + 等价题 → OOD 位置-值
    tr_c = gen_arith(chain_len, 0, 4) + gen_equiv(chain_len, chain_pos, 4)
    run("③ 跨表示桥接 (链长+等价题 → OOD 位置-值)", tr_c, gen_arith(chain_pos, 0, 4))
    # ④ 对称对完全零样本: 训中心≤3 臂≤2 → OOD 中心4..6 臂3..4
    run("④ 对称对完全零样本 (中心≤3 臂≤2 → OOD 中心4..6 臂3..4)",
        gen_sym_pair_train(), gen_sym_pair_ood())
    print("== 完成 ==", flush=True)
