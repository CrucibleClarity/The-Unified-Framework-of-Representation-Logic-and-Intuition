"""zero_succ_exp.py — 0 的 4 种定义 × succ 的 2 种设计对比 (用户指令 2026-08-15)

0 定义 (zero_kind): 公设 0 / 结构 0 / 直觉 0 / 相对 0 (zero_exp 四组)
succ 设计 (succ_kind):
  结构 succ: 数字 n = [succ]×n + [0底] — 后继是显式应用概念 (运算)
  直觉 succ: 数字 n = [one]×n + [0底] — 无 succ token, 后继是原子
             计数 (序列长度 = 数值, 结构直觉)
  直觉 0 组合: 数字 = [one]×n 无底 (0 = 空, 纯 unary)

8 组矩阵: {公设, 结构, 直觉, 相对} 0 × {结构, 直觉} succ
每组: 训练 (加乘 0..4 含 0 全枚举; 相对 0 = 加减+对消) + OOD (5..7 + 0 组合),
完整序列重建判定, 3 seeds.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import inject_dual_tokens
import torch
from train.data import collate, rev_vocab
from train import train_seq

ZERO = None
ZERO_AXIOM = None
SUCC = None
ONE = None
ADD = None
MUL = None
SUB = None


def init():
    global ZERO, ZERO_AXIOM, SUCC, ONE, ADD, MUL, SUB
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")
    ONE = api.eid_by_name("value_one")
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")
    SUB = api.eid_by_name("subtraction")
    inject_dual_tokens({"zero_axiom": {"form": "axiomatic", "arrange": "atom",
                                        "references": []}})
    ZERO_AXIOM = api.eid_by_name("zero_axiom")


def chain(zero_kind, succ_kind, n):
    """数字 n 的表示 (按 0 定义 × succ 设计)."""
    atom = SUCC if succ_kind == "structural" else ONE
    head = [atom] * n
    if zero_kind == "intuitive":
        return head                # 直觉 0: 无底 (0 = 缺省)
    # 公设 0 → zero_axiom; 结构 0 / 相对 0 → value_zero (迭代零点底)
    bottom = ZERO if zero_kind in ("structural", "relative") else ZERO_AXIOM
    return head + [bottom]


def op_sample(zero_kind, succ_kind, op, m, n, k, truth):
    expr = api.assemble_seq(op, [chain(zero_kind, succ_kind, m),
                                 chain(zero_kind, succ_kind, n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"),
                            [expr, chain(zero_kind, succ_kind, k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train(zero_kind, succ_kind, hi=4):
    """加乘 0..4 全枚举 (含 0 的加乘)."""
    out = []
    for m in range(hi + 1):
        for n in range(hi + 1):
            for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
                k = f(m, n)
                out.append(op_sample(zero_kind, succ_kind, op, m, n, k, True))
                out.append(op_sample(zero_kind, succ_kind, op, m, n, k + 1, False))
    return out


def gen_train_rel(succ_kind, himax=4):
    """相对 0: 加法 + 减法对消 (0 从加减法关系定义)."""
    out = []
    for m in range(himax + 1):
        for n in range(himax + 1):
            k = m + n
            out.append(op_sample("structural", succ_kind, ADD, m, n, k, True))
            out.append(op_sample("structural", succ_kind, ADD, m, n, k + 1, False))
    for x in range(1, himax + 1):
        out.append(op_sample("structural", succ_kind, SUB, x, x, 0, True))
        out.append(op_sample("structural", succ_kind, SUB, x, 0, x, True))
    out.append(op_sample("structural", succ_kind, SUB, 0, 0, 0, True))
    return out


def gen_ood(zero_kind, succ_kind, his=(5, 6, 7)):
    """OOD: 训练外数字 + 0 组合."""
    out = []
    for hi in his:
        for m, n in ((hi, hi), (3, hi), (hi, 2), (0, hi), (hi, 0)):
            for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
                k = f(m, n)
                out.append(op_sample(zero_kind, succ_kind, op, m, n, k, True))
                out.append(op_sample(zero_kind, succ_kind, op, m, n, k + 1, False))
    return out


def gen_ood_rel(succ_kind, his=(5, 6, 7)):
    """相对 0 OOD: 纯加减 (训练无乘法)."""
    out = []
    for hi in his:
        for m, n in ((hi, hi), (3, hi), (hi, 2), (0, hi), (hi, 0)):
            k = m + n
            out.append(op_sample("structural", succ_kind, ADD, m, n, k, True))
            out.append(op_sample("structural", succ_kind, ADD, m, n, k + 1, False))
        out.append(op_sample("structural", succ_kind, SUB, hi, hi, 0, True))
        out.append(op_sample("structural", succ_kind, SUB, hi, 0, hi, True))
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


ZERO_KINDS = ("axiomatic", "structural", "intuitive", "relative")
SUCC_KINDS = ("structural", "intuitive")


def run_all(seeds=(0, 1, 2)):
    for zk in ZERO_KINDS:
        for sk in SUCC_KINDS:
            if zk == "relative":
                tr = gen_train_rel(sk)
                od = gen_ood_rel(sk)
            else:
                tr = gen_train(zk, sk)
                od = gen_ood(zk, sk)
            label = f"{zk}0 × {sk}succ"
            print(f"== {label}: 训练 {len(tr)} | OOD {len(od)} ==", flush=True)
            for seed in seeds:
                res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
                evaluate(res["model"], od,
                         f"  seed={seed} 训练acc={res['valid_acc']:.3f} OOD")
            print(flush=True)


if __name__ == "__main__":
    init()
    run_all()
    print("== 完成 ==", flush=True)
