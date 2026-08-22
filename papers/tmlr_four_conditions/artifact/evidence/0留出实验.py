"""zero_hole_exp.py — 0 组合留出实验 (用户指令 2026-08-15)

用户洞察: 之前 OOD 里 0×5 不算真 OOD — 训练已含 0×0..0×4,
模型可从"0 吸收律"类比. 真正的 0 组合 OOD = 部分 0 组合不训练,
测未训练部分能否外推.

设计 (纯结构 succ^n zero, 训练 0..9 加乘全枚举):
  全训组: 0 组合全训 (0×0..0×9, 0+0..0+9, 对称) — 对照组
  留出组: 0×5..0×9, 5×0..9×0, 0+5..0+9, 5+0..9+0 不训练
          (0×0..0×4 等训) — 实验组
OOD: 留出的 0 组合 (0×5..0×9 等) + 训练外数字组合 (10 相关).
测: 模型从少量 0 训练 + 大量非 0 乘法样本, 能否外推 0 吸收律/
单位元律到未训练的 0 组合.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
import torch
from train.data import collate, rev_vocab
from train import train_seq

ZERO = None
SUCC = None
ADD = None
MUL = None


def init():
    global ZERO, SUCC, ADD, MUL
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")


def chain(n):
    return [SUCC] * n + [ZERO]


def op_sample(op, m, n, k, truth):
    expr = api.assemble_seq(op, [chain(m), chain(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train(hi=9, hole=None):
    """加乘 0..hi 全枚举; hole: 留出的 0 组合边界 (k ≥ hole 的 0 侧不训)."""
    out = []
    for m in range(hi + 1):
        for n in range(hi + 1):
            if hole is not None and (m == 0 or n == 0):
                k = max(m, n)
                if k >= hole:
                    continue          # 留出: 0 组合 (k ≥ hole) 不训练
            for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
                k = f(m, n)
                out.append(op_sample(op, m, n, k, True))
                out.append(op_sample(op, m, n, k + 1, False))
    return out


def gen_ood_hole(hi=9, hole=5):
    """留出的 0 组合 (k ≥ hole): 0×5..0×9, 5×0..9×0, 0+5..0+9, 5+0..9+0."""
    out = []
    for k in range(hole, hi + 1):
        for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
            r = f(0, k)
            out.append(op_sample(op, 0, k, r, True))
            out.append(op_sample(op, 0, k, r + 1, False))
            out.append(op_sample(op, k, 0, r, True))
            out.append(op_sample(op, k, 0, r + 1, False))
    return out


def gen_ood_far(his=(10, 11, 12)):
    """训练外数字组合 (对照): 10+2, 10×2 等."""
    out = []
    for m, n in ((10, 2), (2, 10), (10, 0), (0, 10), (11, 2), (10, 3)):
        for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
            k = f(m, n)
            out.append(op_sample(op, m, n, k, True))
            out.append(op_sample(op, m, n, k + 1, False))
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
    for i, s in enumerate(probes):
        L = batch["inputs"].shape[1] - batch["mask"][i].sum().item()
        pred = [rv[p] for p in logits[i, :L].argmax(dim=1).tolist()]
        if all(p == t for p, t in zip(pred, s["seq"])):
            ok += 1
    print(f"{tag}: {ok}/{len(probes)}", flush=True)
    return ok / len(probes)


if __name__ == "__main__":
    init()
    hole_ood = gen_ood_hole()
    far_ood = gen_ood_far()
    print(f"留出 OOD {len(hole_ood)} 条 (0×5..0×9 等) | 训练外数字 OOD {len(far_ood)} 条", flush=True)
    # 对照组: 0 全训
    tr_full = gen_train(hole=None)
    print(f"== 全训组 (0 组合全训, 训练 {len(tr_full)}) ==", flush=True)
    for seed in (0, 1, 2):
        res = train_seq(tr_full, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], far_ood, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 远OOD")
    # 实验组: 0 组合留出 (0×5.. 不训)
    tr_hole = gen_train(hole=5)
    print(f"== 留出组 (0×5..0×9, 0+5..0+9 不训练, 训练 {len(tr_hole)}) ==", flush=True)
    for seed in (0, 1, 2):
        res = train_seq(tr_hole, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], hole_ood, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 留出0OOD")
        evaluate(res["model"], far_ood, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 远OOD")
    print("== 完成 ==", flush=True)
