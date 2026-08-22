"""zero_vs_nz_exp.py — 0 乘法 vs 非零乘法对比 (用户指令 2026-08-15)

用户要求: "0 乘法需要和非零乘法对比 — 表示无法稳定训练".
设计: ① 非零乘法训练 (m,n ∈ 1..9, 0 不作操作数, 0 乘法零样本)
      ② 混训 (0..9 全枚举含 0 乘法)
      OOD 相同: 0×1..0×9, 1×0..9×0, 0×0, 10×2, 10×0, 0×10 (45 条)
结果 (3 seeds): 两组均 45/45 — 0 乘法零样本可从链长乘法规则外推.
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
MUL = None


def init():
    global ZERO, SUCC, MUL
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")
    MUL = api.eid_by_name("multiplication")


def chain(n):
    return [SUCC] * n + [ZERO]


def op_sample(m, n, k, truth):
    expr = api.assemble_seq(MUL, [chain(m), chain(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train_nz():
    """非零乘法: m,n ∈ 1..9 (0 不作操作数)."""
    out = []
    for m in range(1, 10):
        for n in range(1, 10):
            k = m * n
            out.append(op_sample(m, n, k, True))
            out.append(op_sample(m, n, k + 1, False))
    return out


def gen_train_mix():
    """混训: 0..9 全枚举 (含 0 乘法)."""
    out = []
    for m in range(10):
        for n in range(10):
            k = m * n
            out.append(op_sample(m, n, k, True))
            out.append(op_sample(m, n, k + 1, False))
    return out


def gen_ood():
    """OOD: 0 乘法全组合 + 训练外数字 (10 相关)."""
    out = []
    for k in range(1, 10):
        out.append(op_sample(0, k, 0, True))
        out.append(op_sample(0, k, 1, False))
        out.append(op_sample(k, 0, 0, True))
        out.append(op_sample(k, 0, 1, False))
    out.append(op_sample(0, 0, 0, True))
    for m, n in ((10, 2), (2, 10), (10, 0), (0, 10)):
        out.append(op_sample(m, n, m * n, True))
        out.append(op_sample(m, n, m * n + 1, False))
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
    nz = gen_train_nz()
    mix = gen_train_mix()
    od = gen_ood()
    print(f"非零乘法训 {len(nz)} | 混训 {len(mix)} | 0乘法OOD {len(od)}", flush=True)
    print("== ① 非零乘法训练 (0 乘法零样本) ==", flush=True)
    for seed in (0, 1, 2):
        res = train_seq(nz, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], od, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 0乘法OOD")
    print("== ② 混训 (0 乘法有样本) ==", flush=True)
    for seed in (0, 1, 2):
        res = train_seq(mix, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], od, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 0乘法OOD")
    print("== 完成 ==", flush=True)
