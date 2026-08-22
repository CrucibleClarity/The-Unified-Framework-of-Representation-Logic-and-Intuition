"""succ_disc_exp.py — 差异题 (混淆对) 实验 (用户指令 2026-08-15)

差异题: 类似 2×2 vs 2+2 (结果相同), 0×2 vs 0+2 (形式相似结果不同)
— 训练信息必须指向运算的准确结构, 不被结果巧合/形式相似欺骗.

OOD 混淆对: 训练外参数 (0×5=0 vs 0+5=5, 1×6=6 vs 1+6=7,
5×5=25 vs 5+5=10, 3×8 vs 3+8, 0×10 vs 0+10...) 56 条.
测: 运算区分 (加法=链拼接, 乘法=链长乘积) 能否外推到混淆对.
注: 表示内观察 (直觉路径纪律), 不声称跨表示结构 (I7n 判定).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
import torch
from train.data import collate, rev_vocab
from train import train_seq

TOK = {}
ADD = MUL = None


def init():
    global ADD, MUL
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")
    for n in ("succ", "basepoint"):
        TOK[n] = api.eid_by_name(n)


def chain(n):
    return [TOK["succ"]] * n + [TOK["basepoint"]]


def op_sample(op, m, n, k, truth):
    expr = api.assemble_seq(op, [chain(m), chain(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train():
    out = []
    for m in range(10):
        for n in range(10):
            k = m + n
            out.append(op_sample(ADD, m, n, k, True))
            out.append(op_sample(ADD, m, n, k + 1, False))
    for m in range(5):
        for n in range(5):
            k = m * n
            out.append(op_sample(MUL, m, n, k, True))
            out.append(op_sample(MUL, m, n, k + 1, False))
    return out


def gen_disc_train():
    """训练内混淆对: 2×2=4 vs 2+2=4 (结果同), 0×2=0 vs 0+2=2..."""
    out = []
    for m, n in ((2, 2), (0, 2), (2, 0), (0, 0), (1, 1), (0, 1), (1, 0),
                 (2, 1), (1, 2), (3, 0), (0, 3), (3, 1)):
        for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
            k = f(m, n)
            out.append(op_sample(op, m, n, k, True))
            out.append(op_sample(op, m, n, k + 1, False))
    return out


def gen_disc_ood():
    """差异题 OOD: 训练外参数的混淆对 (形式相似结果不同)."""
    out = []
    pairs = [(0, 5), (5, 0), (0, 9), (9, 0), (1, 6), (6, 1), (0, 7), (7, 0),
             (1, 8), (8, 1), (5, 5), (3, 8), (0, 10), (10, 0)]
    for m, n in pairs:
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


if __name__ == "__main__":
    init()
    disc = gen_disc_ood()
    print(f"差异题 OOD {len(disc)} 条 (混淆对: 0×5 vs 0+5, 5×5 vs 5+5...)", flush=True)
    tr = gen_train()
    print(f"== 标准训练 ({len(tr)}) → 差异题 OOD ==", flush=True)
    for seed in (0, 1, 2):
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], disc, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 差异题OOD")
    tr2 = tr + gen_disc_train()
    print(f"== 标准+训练内混淆对 ({len(tr2)}) → 差异题 OOD ==", flush=True)
    for seed in (0, 1, 2):
        res = train_seq(tr2, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], disc, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 差异题OOD")
    print("== 完成 ==", flush=True)
