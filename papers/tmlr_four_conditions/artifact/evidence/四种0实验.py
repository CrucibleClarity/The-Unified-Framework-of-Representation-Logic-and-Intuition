"""zero_exp.py — 四种 0 的定义方式对比实验 (用户指令 2026-08-15)

0 怎么定义? 4 种定义 → 可学习性/外推对比:
  ① 公设 0 : zero_axiom (C 层临时注入, form=axiomatic 无定义) — 0 直接给定
  ② 结构 0 : value_zero (迭代零点: iterate(iteration_layer)) — 0 从迭代
             结构定义 (既有定义, succ_nest 基线)
  ③ 直觉 0 : 空链 (数字 n = succ^n, 0 = 无 successor) — 0 无 token,
             从结构缺省推断 (op 后参数缺失 = 0)
  ④ 相对 0 : value_zero 底 + 训练含减法对消 (x-x=0, x-0=x) — 0 从
             加减法关系定义 (单位元/对消律)

每组: 训练加乘 0..4 全枚举 (含 0) + OOD (5..7 训练外数字 + 0 组合),
完整序列重建判定, 3 seeds. 对比: 收敛率 + 外推率.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import inject_dual_tokens
import torch
from train.data import collate, rev_vocab
from train import train_seq

ZERO = None          # 结构 0 (value_zero, 迭代零点)
ZERO_AXIOM = None    # 公设 0 (临时注入 axiomatic)
SUCC = None
ADD = None
MUL = None
SUB = None


def init():
    global ZERO, ZERO_AXIOM, SUCC, ADD, MUL, SUB
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")
    SUB = api.eid_by_name("subtraction")
    # 公设 0: axiomatic 无定义 (C 层临时注入, 幂等)
    inject_dual_tokens({"zero_axiom": {"form": "axiomatic", "arrange": "atom",
                                        "references": []}})
    ZERO_AXIOM = api.eid_by_name("zero_axiom")


def chain(kind, n):
    """数字 n 的表示 (按 0 的定义方式)."""
    if kind == "intuitive":
        return [SUCC] * n          # 直觉 0: 无底 (0 = 缺省)
    bottom = ZERO if kind == "structural" else ZERO_AXIOM
    return [SUCC] * n + [bottom]   # 结构 0 / 公设 0: succ^n(0)


def op_sample(kind, op, m, n, k, truth):
    expr = api.assemble_seq(op, [chain(kind, m), chain(kind, n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(kind, k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train(kind, hi=4):
    """加乘 0..4 全枚举 (含 0 的加乘)."""
    out = []
    for m in range(hi + 1):
        for n in range(hi + 1):
            for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
                k = f(m, n)
                out.append(op_sample(kind, op, m, n, k, True))
                out.append(op_sample(kind, op, m, n, k + 1, False))
    return out


def gen_train_rel(himax=4):
    """④ 相对 0: 加法 + 减法对消 (0 从加减法关系定义)."""
    out = []
    for m in range(himax + 1):
        for n in range(himax + 1):
            k = m + n
            out.append(op_sample("structural", ADD, m, n, k, True))
            out.append(op_sample("structural", ADD, m, n, k + 1, False))
    for x in range(1, himax + 1):            # x-x=0 (对消), x-0=x
        out.append(op_sample("structural", SUB, x, x, 0, True))
        out.append(op_sample("structural", SUB, x, 0, x, True))
    out.append(op_sample("structural", SUB, 0, 0, 0, True))
    return out


def gen_ood(kind, his=(5, 6, 7)):
    """OOD: 训练外数字 + 0 组合."""
    out = []
    for hi in his:
        for m, n in ((hi, hi), (3, hi), (hi, 2), (0, hi), (hi, 0)):
            for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
                k = f(m, n)
                out.append(op_sample(kind, op, m, n, k, True))
                out.append(op_sample(kind, op, m, n, k + 1, False))
    return out


def gen_ood_rel(his=(5, 6, 7)):
    """④ OOD: 纯加减 (训练无乘法 — OOD 不含乘法)."""
    out = []
    for hi in his:
        for m, n in ((hi, hi), (3, hi), (hi, 2), (0, hi), (hi, 0)):
            k = m + n
            out.append(op_sample("structural", ADD, m, n, k, True))
            out.append(op_sample("structural", ADD, m, n, k + 1, False))
        out.append(op_sample("structural", SUB, hi, hi, 0, True))
        out.append(op_sample("structural", SUB, hi, 0, hi, True))
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


def run(kind, train_s, ood_s, seeds=(0, 1, 2)):
    print(f"== {kind}: 训练 {len(train_s)} | OOD {len(ood_s)} ==", flush=True)
    for seed in seeds:
        res = train_seq(train_s, epochs=60, dim=64, num_layers=2, seed=seed)
        ok = evaluate(res["model"], ood_s, f"  seed={seed} 训练acc={res['valid_acc']:.3f} OOD")
    print(flush=True)


if __name__ == "__main__":
    init()
    run("① 公设 0 (axiomatic)", gen_train("axiomatic"), gen_ood("axiomatic"))
    run("② 结构 0 (迭代零点)", gen_train("structural"), gen_ood("structural"))
    run("③ 直觉 0 (空链缺省)", gen_train("intuitive"), gen_ood("intuitive"))
    run("④ 相对 0 (加减法对消)", gen_train_rel(), gen_ood_rel())
    print("== 完成 ==", flush=True)
