"""E16_disc_zero_pole.py — E13 差异题的 0 极对照 (两极对比纪律 I7ag)

E13 (1 极): 标准训练 (真+假) → 差异题混淆对 OOD 56/56 (运算区分可外推)。
缺失 0 极: 训练无假样本 (无冲突声明信息) → OOD 混淆对判定?

设计 (伪恢复排除三件套 B2: 错题必须):
  ① 0 极: 训练只含真样本 (无假) → OOD 混淆对 (真+假混合) — 期望全判真 (崩)
  ② 1 极对照: 标准训练 (E13 已有 56/56, 引用)
预期: 无假样本 → truth bias → OOD 混淆对假样本判真 → 判定 0/56 或部分
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
import torch
from train.data import collate, rev_vocab
from train import train_seq

ADD = MUL = None


def init():
    global ADD, MUL
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")


def chain(n):
    succ = api.eid_by_name("succ")
    bp = api.eid_by_name("basepoint")
    return [succ] * n + [bp]


def op_sample(op, m, n, k, truth):
    expr = api.assemble_seq(op, [chain(m), chain(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train(hi_add=9, hi_mul=4, with_false=True):
    """标准加法/乘法枚举; with_false=False = 只真样本 (无冲突声明)."""
    out = []
    for m in range(hi_add + 1):
        for n in range(hi_add + 1):
            k = m + n
            out.append(op_sample(ADD, m, n, k, True))
            if with_false:
                out.append(op_sample(ADD, m, n, k + 1, False))
    for m in range(hi_mul + 1):
        for n in range(hi_mul + 1):
            k = m * n
            out.append(op_sample(MUL, m, n, k, True))
            if with_false:
                out.append(op_sample(MUL, m, n, k + 1, False))
    return out


def gen_disc_ood():
    """差异题混淆对 OOD (与 E13 相同): 0×5 vs 0+5, 5×5 vs 5+5..."""
    pairs = [(0, 5), (5, 0), (5, 5), (2, 5), (5, 2), (1, 6), (6, 1)]
    out = []
    for m, n in pairs:
        out.append(op_sample(MUL, m, n, m * n, True))   # × 真
        out.append(op_sample(MUL, m, n, m * n + 1, False))  # × 假
        out.append(op_sample(ADD, m, n, m + n, True))   # + 真
        out.append(op_sample(ADD, m, n, m + n + 1, False))  # + 假
    return out


def evaluate(model, probes, tag):
    rv = rev_vocab()
    batch = collate(probes, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v) for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    ok = 0
    truth_ok = 0
    truth_n = 0
    for i, s in enumerate(probes):
        L = batch["inputs"].shape[1] - batch["mask"][i].sum().item()
        pred = [rv[p] for p in logits[i, :L].argmax(dim=1).tolist()]
        if all(p == t for p, t in zip(pred, s["seq"])):
            ok += 1
        # 真值位置判定 (末尾真值)
        tv = s["valid"]
        pv = 1 if pred[-1] == s["seq"][-1] else 0
        # 简化: 用末尾真值 token 判定
    print(f"{tag}: {ok}/{len(probes)}", flush=True)


def run(label, tr, od, n_seed=3):
    print(f"== {label}: 训练 {len(tr)} ==", flush=True)
    for seed in range(n_seed):
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], od, f"  seed={seed} 训练acc={res['valid_acc']:.3f} OOD")


if __name__ == "__main__":
    init()
    ood = gen_disc_ood()
    # ① 0 极: 只真样本 (无假, 无冲突声明) → OOD 混淆对
    run("① 0 极: 训真样本 (无假) → OOD 差异题混淆对", gen_train(with_false=False), ood)
    print("== 完成 ==", flush=True)
