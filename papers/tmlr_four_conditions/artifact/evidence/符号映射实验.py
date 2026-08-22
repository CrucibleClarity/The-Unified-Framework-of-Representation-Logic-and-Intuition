"""sym_map_exp.py — 符号映射实验: 表达与概念分离 (用户指令 2026-08-14)

用户断言: 数轴上的自然数符号映射没法稳定学习 — 位置不变数值变
(同一 digit 符号在不同位置代表不同值) = 表达与概念的分离.
stoken 需映射到 ctoken (符号对应语义); 跨层映射需显式结构承载.

三组对照 (训练 0..49, OOD 测 50..99 两位数 + 100..999 三位数):
  A 符号→概念 (跨层): [is_true][symbol_1][symbol_2][=][概念结构 12][truth]
      裸 glyph 序列 (S 层) 解码位置-值 → 概念结构 (C 层 numeral)
  C 概念→概念 (同层): [is_true][概念 12][=][概念 12][truth] (+错题)
      概念结构内位置-值比较 (无跨层, 无运算)
  B 运算判定 (基线): neg 对错题 (既有 gen_samples, 已知稳定 1.000)

判据: OOD 完整序列重建率. A 崩 C 稳 → 跨层映射不稳 (表达/概念分离:
符号侧只有统计表, 无位置-值组合机制外推); A 崩 C 崩 → 位置-值组合
本身需显式结构 (与层无关).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample, gen_samples
from lab.judge import judge_sequence
from lab.synth_core import numeral_of
import torch
from train.data import collate, rev_vocab
from train import train_seq


def sym_seq(n):
    """裸符号序列 (S 层 glyph): 数字 n 的高→低 digit 符号."""
    return [api.eid_by_name(f"symbol_numeral_{d}") for d in map(int, str(n))]


def wrap(seq):
    return api.assemble_seq(api.role_token("bracket"), [seq])


def eq_prop(lhs, rhs):
    return api.assemble_seq(api.role_token("equals"), [lhs, rhs])


def gen_A(hi=49):
    """A: 符号→概念 (跨层). 真: 符号 n = 概念 n; 错: 符号 n = 概念 n+1."""
    out = []
    for n in range(hi + 1):
        lhs = wrap(sym_seq(n))
        out.append(make_sample(judge_sequence(eq_prop(lhs, numeral_of(n)), True), True, 0))
        out.append(make_sample(judge_sequence(eq_prop(lhs, numeral_of(n + 1)), False), False, 0))
    return out


def gen_C(hi=49):
    """C: 概念→概念 (同层). 真: 概念 n = 概念 n; 错: 概念 n = 概念 n+1."""
    out = []
    for n in range(hi + 1):
        out.append(make_sample(judge_sequence(eq_prop(numeral_of(n), numeral_of(n)), True), True, 0))
        out.append(make_sample(judge_sequence(eq_prop(numeral_of(n), numeral_of(n + 1)), False), False, 0))
    return out


def gen_B():
    """B: 运算判定基线 (neg 对错题)."""
    return gen_samples(api.eid_by_name("neg"), 9)[0]


def ood_probes():
    """OOD 探针 (A 形式): 训练外两位数 (50..99) + 三位数 (100..999)."""
    out = []
    for n in list(range(50, 100, 5)) + [123, 456, 789, 999, 321]:
        out.append(make_sample(judge_sequence(eq_prop(wrap(sym_seq(n)), numeral_of(n)), True), True, 0))
    return out


def ood_probes_C():
    """OOD 探针 (C 形式, 同层): 概念 n = 概念 n (真) + 概念 n = 概念 n+1 (假)."""
    out = []
    for n in list(range(50, 100, 5)) + [123, 456, 789, 999, 321]:
        out.append(make_sample(judge_sequence(eq_prop(numeral_of(n), numeral_of(n)), True), True, 0))
        out.append(make_sample(judge_sequence(eq_prop(numeral_of(n), numeral_of(n + 1)), False), False, 0))
    return out


def evaluate(label, model, probes):
    batch = collate(probes, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v) for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    rv = rev_vocab()
    ok = 0
    for i, s in enumerate(probes):
        L = batch["inputs"].shape[1] - batch["mask"][i].sum().item()
        pred = [rv[p] for p in logits[i, :L].argmax(dim=1).tolist()]
        if all(p == t for p, t in zip(pred, s["seq"])):
            ok += 1
    print(f"{label}: {ok}/{len(probes)}", flush=True)
    return ok / len(probes)


def run(label, samples, probes, epochs=30, seed=0):
    res = train_seq(samples, epochs=epochs, dim=64, num_layers=2, seed=seed)
    print(f"{label}: 训练 acc={res['valid_acc']:.3f}", flush=True)
    return evaluate(label + " OOD", res["model"], probes)


if __name__ == "__main__":
    probes_a = ood_probes()
    probes_c = ood_probes_C()
    print(f"A OOD 探针 {len(probes_a)} 条 | C OOD 探针 {len(probes_c)} 条", flush=True)
    run("A 符号→概念 (跨层)", gen_A(), probes_a)
    run("C 概念→概念 (同层)", gen_C(), probes_c)
    print("== 完成 ==", flush=True)
