"""E17两极预声明实验.py — 两极预声明合规重做 (2026-08-16 方法论改进)

覆盖检查暴露 E13/E14 单极问题后, 按新规范 (两极预声明: 设计时声明
0 极/1 极条件, 跑完两列齐备) 重做。三组六条件:

E17a 等价性两极 (E4+E6 合并):
  预声明 1 极: 四种 0 定义 × 链长 (A 型) → OOD 全过 (定义层不可见)
  预声明 0 极: 四种 0 定义 × 裸符号 (B 型) → OOD 崩 (表示层可见)
E17b 差异题两极 (E13+E16 合并):
  预声明 1 极: 标准训练 (真+假) → 差异题混淆对全过 (冲突声明显式)
  预声明 0 极: 无假样本训练 → 差异题混淆对崩 (truth bias, 无冲突信息)
E17c 对称中心两极 (E14+E15 合并):
  预声明 1 极: 链长中点 → OOD 全过 (中心 = 链长算术, 可外推)
  预声明 0 极: 跨表示中点 (位置-值) → OOD 崩 (表示绑定, 格式层)

跑完核对: 每组的 0 极/1 极两列必须齐备。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import numeral_of, inject_dual_tokens
import torch
from train.data import collate, rev_vocab
from train import train_seq

ADD = MUL = MID = None
ZERO = SUCC = None
ZERO_AXIOM = None


def init():
    global ADD, MUL, MID, ZERO, SUCC, ZERO_AXIOM
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")
    MID = api.eid_by_name("midpoint")
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")
    inject_dual_tokens({
        "zero_axiom": {"form": "axiomatic", "arrange": "atom", "references": []},
        **{f"symbol_numeral_{d}": {"form": "explicit", "arrange": "atom",
                                     "rules": [{"term": ["D:127"]}],
                                     "references": ["D:127"]} for d in range(10)},
    })
    ZERO_AXIOM = api.eid_by_name("zero_axiom")


def chain_A(n):
    """链长 (纯结构): succ^n zero."""
    return [SUCC] * n + [ZERO]


def chain_B(n):
    """裸符号 (B 型): symbol_numeral 序列 — 位置不变数值变."""
    return [api.eid_by_name(f"symbol_numeral_{d}") for d in [int(c) for c in str(n)]]


def chain_P(n):
    """位置-值 (C 型): numeral 结构."""
    return numeral_of(n)


def zero_token(kind):
    """四种 0 定义 (0 token 选择, 与表示无关):
    axiom=zero_axiom (公设), struct=value_zero (迭代零点),
    empty=无 token (空链缺省), rel=value_zero (相对 0, 对消律定义)."""
    if kind == "axiom":
        return [ZERO_AXIOM]
    if kind == "empty":
        return []
    return [ZERO]


def gen_zero4_one(ch, kind, lo=0, hi=2):
    """单种 0 定义 × 表示 ch: 操作数非 0 用 ch(m), 0 用该定义 0 token;
    输出同表示. 真 OOD: 训 [0,2] 测 [0,4] (表示 token 外推)."""
    out = []
    c0 = zero_token(kind)
    for m in range(lo, hi + 1):
        for n in range(lo, hi + 1):
            k = m + n
            op_m = c0 if m == 0 else ch(m)
            op_n = c0 if n == 0 else ch(n)
            res = c0 if k == 0 else ch(k)
            expr = api.assemble_seq(ADD, [op_m, op_n])
            expr = api.assemble_seq(api.role_token("bracket"), [expr])
            prop = api.assemble_seq(api.role_token("equals"), [expr, res])
            out.append(make_sample(judge_sequence(prop, True), True, 2))
            out.append(make_sample(judge_sequence(prop, False), False, 2))
    return out


def run_zero4(label, ch, n_seed=3):
    """四种 0 定义 × 表示 ch: 每定义独立训练, OOD 真外推."""
    for kind in ("axiom", "struct", "empty", "rel"):
        run(f"{label} [{kind}]", gen_zero4_one(ch, kind, 0, 2), gen_zero4_one(ch, kind, 0, 4), n_seed)


def op_sample(ch, op, m, n, k, truth):
    expr = api.assemble_seq(op, [ch(m), ch(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, ch(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_arith(ch, hi=4, with_false=True):
    out = []
    for m in range(hi + 1):
        for n in range(hi + 1):
            k = m + n
            out.append(op_sample(ch, ADD, m, n, k, True))
            if with_false:
                out.append(op_sample(ch, ADD, m, n, k + 1, False))
    for m in range(hi + 1):
        for n in range(hi + 1):
            k = m * n
            out.append(op_sample(ch, MUL, m, n, k, True))
            if with_false:
                out.append(op_sample(ch, MUL, m, n, k + 1, False))
    return out


def gen_zero4(ch, lo=0, hi=2):
    """四种 0 定义 × 表示 ch: 加乘 [lo,hi] 全枚举 (真 OOD: 训 [0,2], 测 [0,4])."""
    out = []
    for kind in ("axiom", "struct", "empty", "rel"):
        c0 = chain0(kind, 0)
        for m in range(lo, hi + 1):
            for n in range(lo, hi + 1):
                k = m + n
                expr = api.assemble_seq(ADD, [c0 if m == 0 else chain_A(m),
                                              c0 if n == 0 else chain_A(n)])
                expr = api.assemble_seq(api.role_token("bracket"), [expr])
                prop = api.assemble_seq(api.role_token("equals"), [expr, chain_A(k)])
                out.append(make_sample(judge_sequence(prop, True), True, 2))
    return out


def gen_disc_ood():
    pairs = [(0, 5), (5, 0), (5, 5), (2, 5), (5, 2), (1, 6), (6, 1)]
    out = []
    for m, n in pairs:
        out.append(op_sample(chain_A, MUL, m, n, m * n, True))
        out.append(op_sample(chain_A, MUL, m, n, m * n + 1, False))
        out.append(op_sample(chain_A, ADD, m, n, m + n, True))
        out.append(op_sample(chain_A, ADD, m, n, m + n + 1, False))
    return out


def gen_mid(ch, lo, hi):
    out = []
    for a in range(lo, hi + 1):
        for b in range(lo, hi + 1):
            if (a + b) % 2:
                continue
            k = (a + b) // 2
            out.append(op_sample(ch, MID, a, b, k, True))
            out.append(op_sample(ch, MID, a, b, k + 1, False))
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


def run(label, tr, od, n_seed=3):
    print(f"== {label}: 训练 {len(tr)} ==", flush=True)
    for seed in range(n_seed):
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], od, f"  seed={seed} 训练acc={res['valid_acc']:.3f} OOD")


if __name__ == "__main__":
    init()
    # ===== E17a 等价性两极 =====
    run_zero4("E17a-1极 四种 0 × 链长 (定义层不可见, 期望全过)", chain_A)
    run_zero4("E17a-0极 四种 0 × 裸符号 (表示层可见, 期望崩)", chain_B)
    # ===== E17b 差异题两极 =====
    run("E17b-1极 标准训练 (真+假) → 差异题混淆对 (期望全过)",
        gen_arith(chain_A, 4), gen_disc_ood())
    run("E17b-0极 无假样本 → 差异题混淆对 (期望崩 truth bias)",
        gen_arith(chain_A, 4, with_false=False), gen_disc_ood())
    # ===== E17c 对称中心两极 =====
    run("E17c-1极 链长中点 → OOD 中心漂移 (期望全过)",
        gen_mid(chain_A, 0, 4), gen_mid(chain_A, 5, 7))
    run("E17c-0极 跨表示中点 (位置-值) → OOD (期望崩)",
        gen_mid(chain_A, 0, 4), gen_mid(chain_P, 0, 4))
    print("== 完成 ==", flush=True)
