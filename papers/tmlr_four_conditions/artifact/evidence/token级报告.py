"""token_report.py — 关键对比的 token 级报告 (用户纪律 2026-08-15)

所有实证必须对比出干净结果: 样本全对数 + token 对/总数 + 位置正确率
(崩点定位). 覆盖关键对比:
  A 同锚桥接 (E12): ①a 基线 / ①b 零样本 / ② 等价声明桥接
  B 锚漂移 (E11): 同锚 / 跨锚零样本 / 显式穿折越桥接
  C 差异题 (E13): 标准训练 → 混淆对 OOD
  D 跨表示剥离 (I7n): 同表示 / 迭代表达 / 位置-值记法
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import numeral_of, inject_dual_tokens
from train.data import collate, rev_vocab
from train import train_seq
import torch

SUCC = None; BP = None; Z = None; IT = None
ADD = None; MUL = None
SA = None; SB = None


def init():
    global SUCC, BP, Z, IT, ADD, MUL, SA, SB
    SUCC = api.eid_by_name("succ"); BP = api.eid_by_name("basepoint")
    Z = api.eid_by_name("value_zero"); IT = api.eid_by_name("iterate")
    ADD = api.eid_by_name("addition"); MUL = api.eid_by_name("multiplication")
    inject_dual_tokens({
        "succ_a": {"form": "explicit", "arrange": "application",
                   "rules": [{"term": ["D:194"]}], "references": ["D:194"]},
        "succ_b": {"form": "explicit", "arrange": "application",
                   "rules": [{"term": ["D:194"]}], "references": ["D:194"]},
        "basepoint_f": {"form": "axiomatic", "arrange": "atom", "references": []},
    })
    SA = api.eid_by_name("succ_a"); SB = api.eid_by_name("succ_b")
    BPF = api.eid_by_name("basepoint_f")


def chain_a(n): return [SUCC] * n + [BP]
def chain_sa(n): return [SA] * n + [BP]
def chain_sb(n): return [SB] * n + [BP]
def chain_f(n): return [SUCC] * n + [api.eid_by_name("basepoint_f")]
def chain_b(n): return api.assemble_seq(IT, [[SUCC], [SUCC] * n + [Z], [BP]])
def chain_c(n): return numeral_of(n)


def op_sample(ch, op, m, n, k, truth):
    expr = api.assemble_seq(op, [ch(m), ch(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, ch(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_arith(ch, hi_add=9, hi_mul=4):
    out = []
    for m in range(hi_add + 1):
        for n in range(hi_add + 1):
            k = m + n
            out.append(op_sample(ch, ADD, m, n, k, True))
            out.append(op_sample(ch, ADD, m, n, k + 1, False))
    for m in range(hi_mul + 1):
        for n in range(hi_mul + 1):
            k = m * n
            out.append(op_sample(ch, MUL, m, n, k, True))
            out.append(op_sample(ch, MUL, m, n, k + 1, False))
    return out


def gen_equiv():
    out = []
    for n in range(10):
        prop = api.assemble_seq(api.role_token("equals"), [chain_sa(n), chain_sb(n)])
        out.append(make_sample(judge_sequence(prop, True), True, 1))
    return out


def gen_ood(ch):
    out = []
    for m, n in ((10, 2), (2, 10), (10, 3), (3, 10), (11, 2), (12, 2), (5, 3), (6, 2)):
        for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
            k = f(m, n)
            out.append(op_sample(ch, op, m, n, k, True))
            out.append(op_sample(ch, op, m, n, k + 1, False))
    return out


def evaluate_tok(model, probes, tag):
    rv = rev_vocab()
    batch = collate(probes, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v) for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    per_ok, per_tot, samples = [], [], []
    for i, s in enumerate(probes):
        L = batch["inputs"].shape[1] - batch["mask"][i].sum().item()
        pred = [rv[p] for p in logits[i, :L].argmax(dim=1).tolist()]
        ok = [p == t for p, t in zip(pred, s["seq"])]
        samples.append((sum(ok), len(ok)))
        while len(per_ok) < len(ok):
            per_ok.append(0); per_tot.append(0)
        for j, o in enumerate(ok):
            per_ok[j] += o; per_tot[j] += 1
    t_ok = sum(a for a, _ in samples); t_tot = sum(b for _, b in samples)
    print(f"{tag}: 样本全对 {sum(1 for a, b in samples if a == b)}/{len(probes)}"
          f" | token {t_ok}/{t_tot} ({t_ok / t_tot:.2f})", flush=True)
    print("   位置: " + " ".join(f"{per_ok[j]}/{per_tot[j]}" for j in range(min(22, len(per_ok)))), flush=True)


def run(label, tr, od, seeds=(0,)):
    print(f"== {label} ==", flush=True)
    for seed in seeds:
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate_tok(res["model"], od, f"  seed={seed}")


def gen_disc():
    """差异题混淆对 OOD (E13): 0×5 vs 0+5, 5×5 vs 5+5 等训练外参数."""
    out = []
    for m, n in ((0, 5), (5, 0), (0, 9), (1, 6), (5, 5), (3, 8), (0, 10)):
        for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
            k = f(m, n)
            out.append(op_sample(chain_a, op, m, n, k, True))
            out.append(op_sample(chain_a, op, m, n, k + 1, False))
    return out


if __name__ == "__main__":
    init()
    # A 同锚桥接 (E12)
    run("A1 训 succ_a → OOD succ_a (基线)", gen_arith(chain_sa), gen_ood(chain_sa))
    run("A2 训 succ_a → OOD succ_b (同基点零样本)", gen_arith(chain_sa), gen_ood(chain_sb))
    run("A3 训 succ_a + 等价声明 → OOD succ_b (桥接)", gen_arith(chain_sa) + gen_equiv(), gen_ood(chain_sb))
    # B 锚漂移 (E11)
    run("B1 锚 basepoint → OOD 同锚 (基线)", gen_arith(chain_a), gen_ood(chain_a))
    run("B2 锚 basepoint → OOD 锚 f (跨锚零样本)", gen_arith(chain_a), gen_ood(chain_f))
    # C 差异题 (E13)
    run("C 标准训练 → 差异题混淆对 OOD", gen_arith(chain_a), gen_disc())
    # D 跨表示剥离 (I7n)
    run("D1 应用链 → 同表示 OOD", gen_arith(chain_a), gen_ood(chain_a))
    run("D2 应用链 → 迭代表达 OOD (跨表示)", gen_arith(chain_a), gen_ood(chain_b))
    run("D3 应用链 → 位置-值记法 OOD (跨表示)", gen_arith(chain_a), gen_ood(chain_c))
    print("== 完成 ==", flush=True)
