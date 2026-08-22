"""zero_symbol_exp.py — 结构直觉 vs 符号 token 对比 (用户指令 2026-08-15)

用户要点:
  ① 训练样本不只 0/2 相关 — 扩到 0..9 加乘全枚举 (400 样本)
  ② 对比符号 token: 位置不变、数值改变 (位置-值记法) — 没有符号
     只有 ctoken 是否不行
  ③ 每个数值设计一个位置 (显式位置 token) / numeral 本身就是直觉路径

4 组表示 (0 = value_zero, 数字 n):
  A 纯结构直觉: [succ]×n + [zero] — 无符号无位置 (同构嵌套)
  B 符号裸:     symbol_numeral 序列 (S 层 glyph) — 位置不变数值变
  C numeral 结构: numeral_of(n) — C 层位置-值 (digit 排序 = 位权,
                "numeral 本身就是直觉路径")
  D 显式位置:   [symbol_d][place_p] 对 (注入 place_0..2 概念) —
                每个数值配显式位置 token

训练 0..9 加乘全枚举 (含 0); OOD 10..15 (训练外, 含位置-值外推)
+ 0 组合 (0+10, 10+0, 0×10, 10×0). 完整序列重建, 3 seeds.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import numeral_of, inject_dual_tokens
import torch
from train.data import collate, rev_vocab
from train import train_seq

ZERO = None
SUCC = None
ADD = None
MUL = None
PLACE = {}


def init():
    global ZERO, SUCC, ADD, MUL, PLACE
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")
    inject_dual_tokens({
        f"place_{p}": {"form": "explicit", "arrange": "atom",
                        "references": []} for p in (0, 1, 2)})
    for p in (0, 1, 2):
        PLACE[p] = api.eid_by_name(f"place_{p}")


def digits(n):
    return [int(d) for d in str(n)]


def chain_A(n):
    """纯结构: succ^n zero."""
    return [SUCC] * n + [ZERO]


def chain_B(n):
    """符号裸: symbol_numeral 序列 (S 层 glyph, 高→低)."""
    return [api.eid_by_name(f"symbol_numeral_{d}") for d in digits(n)]


def chain_C(n):
    """numeral 结构: C 层位置-值 (digit 排序 = 位权)."""
    return numeral_of(n)


def chain_D(n):
    """显式位置: [symbol_d][place_p] 对 (高→低, 位置 token 显式)."""
    ds = digits(n)
    out = []
    for i, d in enumerate(ds):
        p = len(ds) - 1 - i          # 位权: 最高位 = 位数-1
        out.append(api.eid_by_name(f"symbol_numeral_{d}"))
        out.append(PLACE[p])
    return out


CHAINS = {"A": chain_A, "B": chain_B, "C": chain_C, "D": chain_D}


def op_sample(kind, op, m, n, k, truth):
    ch = CHAINS[kind]
    expr = api.assemble_seq(op, [ch(m), ch(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, ch(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train(kind):
    """加法 0..9 全枚举 (两位数外推目标) + 乘法 0..4 (输出链 ≤ 16)."""
    out = []
    for m in range(10):
        for n in range(10):
            k = m + n
            out.append(op_sample(kind, ADD, m, n, k, True))
            out.append(op_sample(kind, ADD, m, n, k + 1, False))
    for m in range(5):
        for n in range(5):
            k = m * n
            out.append(op_sample(kind, MUL, m, n, k, True))
            out.append(op_sample(kind, MUL, m, n, k + 1, False))
    return out


def gen_ood(kind):
    """OOD: 加法两位数组合 (位置-值外推) + 乘法 5..6 (输出 ≤ 18 链)."""
    out = []
    for m, n in ((10, 2), (2, 10), (10, 3), (3, 10), (0, 10), (10, 0),
                 (11, 2), (2, 11), (12, 2)):
        k = m + n
        out.append(op_sample(kind, ADD, m, n, k, True))
        out.append(op_sample(kind, ADD, m, n, k + 1, False))
    for m, n in ((5, 3), (3, 5), (5, 2), (0, 5), (5, 0), (6, 2)):
        k = m * n
        out.append(op_sample(kind, MUL, m, n, k, True))
        out.append(op_sample(kind, MUL, m, n, k + 1, False))
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
    for kind, desc in (("A", "纯结构 succ^n zero"), ("B", "符号裸 glyph 序列"),
                       ("C", "numeral 结构 (直觉路径)"), ("D", "显式位置 [symbol][place]")):
        tr = gen_train(kind)
        od = gen_ood(kind)
        mx = max(len(s["seq"]) for s in tr + od)
        print(f"== {kind} {desc}: 训练 {len(tr)} | OOD {len(od)} | 最长 {mx} tokens ==", flush=True)
        for seed in (0, 1, 2):
            res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
            evaluate(res["model"], od,
                     f"  seed={seed} 训练acc={res['valid_acc']:.3f} OOD")
        print(flush=True)
    print("== 完成 ==", flush=True)
