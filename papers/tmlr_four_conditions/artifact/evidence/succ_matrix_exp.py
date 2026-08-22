"""succ_matrix_exp.py — succ 结构对比矩阵 (用户指令 2026-08-15)

设计纪律 (用户): 没做完整消融对比前必须假设所有 OOD 是直觉;
差别只有通过对比产生; 对错题/对比题让训练信息指向准确结构.

succ 家族: succ_a/succ_b (同基点 basepoint, 2 种) +
           succ_c/succ_d (锚 basepoint_c/d, 3 种不同)
对错题设计: 锚定错题 (锚基点链 ≠ 锚 value_zero 链 = 假) +
           等价对比题 (同基点 succ 链 = 等价声明)

对比 (每对理论差别明确):
  ① 同基点 2 succ: 1a 训 succ_a→OOD succ_a (基线) vs
                    1b 训 succ_a→OOD succ_b (零样本)
  ② 等价声明桥接: 1c 训 succ_a + 等价题→OOD succ_b
  ④ 对称性专用: 4a 加乘同 succ vs 4b 加法 succ_a/乘法 succ_b
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import inject_dual_tokens
import torch
from train.data import collate, rev_vocab
from train import train_seq

TOK = {}
ADD = MUL = None


def init():
    global ADD, MUL
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")
    inject_dual_tokens({
        "succ_a": {"form": "explicit", "arrange": "application",
                   "rules": [{"term": ["D:194"]}], "references": ["D:194"]},
        "succ_b": {"form": "explicit", "arrange": "application",
                   "rules": [{"term": ["D:194"]}], "references": ["D:194"]},
        "basepoint_c": {"form": "axiomatic", "arrange": "atom", "references": []},
        "succ_c": {"form": "explicit", "arrange": "application",
                   "rules": [{"term": ["D:194"]}], "references": ["D:194"]},
    })
    for n in ("succ_a", "succ_b", "succ_c", "basepoint", "basepoint_c",
              "value_zero"):
        TOK[n] = api.eid_by_name(n)


def chain(succ, bp, n):
    return [TOK[succ]] * n + [TOK[bp]]


def eq_prop(lhs, rhs):
    return api.assemble_seq(api.role_token("equals"), [lhs, rhs])


def op_sample(succ, bp, op, m, n, k, truth):
    expr = api.assemble_seq(op, [chain(succ, bp, m), chain(succ, bp, n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = eq_prop(expr, chain(succ, bp, k))
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_arith(succ, bp, hi_add=9, hi_mul=4):
    out = []
    for m in range(hi_add + 1):
        for n in range(hi_add + 1):
            k = m + n
            out.append(op_sample(succ, bp, ADD, m, n, k, True))
            out.append(op_sample(succ, bp, ADD, m, n, k + 1, False))
    for m in range(hi_mul + 1):
        for n in range(hi_mul + 1):
            k = m * n
            out.append(op_sample(succ, bp, MUL, m, n, k, True))
            out.append(op_sample(succ, bp, MUL, m, n, k + 1, False))
    return out


def gen_equiv(succ1, succ2, hi=9):
    """等价对比题: succ1 链 n = succ2 链 n (同基点 succ 等价声明)."""
    out = []
    for n in range(hi + 1):
        prop = eq_prop(chain(succ1, "basepoint", n), chain(succ2, "basepoint", n))
        out.append(make_sample(judge_sequence(prop, True), True, 1))
    return out


def gen_anchor_wrong(succ, hi=4):
    """锚定错题: 锚基点链 ≠ 锚 value_zero 链 (锚定不同 = 假)."""
    out = []
    for n in range(hi + 1):
        prop = eq_prop(chain(succ, "basepoint", n), chain(succ, "value_zero", n))
        out.append(make_sample(judge_sequence(prop, False), False, 1))
    return out


def gen_ood(succ, bp):
    out = []
    for m, n in ((10, 2), (2, 10), (10, 3), (3, 10), (11, 2), (12, 2), (5, 3), (6, 2)):
        for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
            k = f(m, n)
            out.append(op_sample(succ, bp, op, m, n, k, True))
            out.append(op_sample(succ, bp, op, m, n, k + 1, False))
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
    ood_a = gen_ood("succ_a", "basepoint")
    ood_b = gen_ood("succ_b", "basepoint")
    # ① 同基点 2 succ
    run("①a 训 succ_a → OOD succ_a (基线)", gen_arith("succ_a", "basepoint"), ood_a)
    run("①b 训 succ_a → OOD succ_b (同基点零样本)", gen_arith("succ_a", "basepoint"), ood_b)
    # ② 等价声明桥接 (对比题: 同基点等价 + 锚定错题)
    tr_c = gen_arith("succ_a", "basepoint") + gen_equiv("succ_a", "succ_b") \
           + gen_anchor_wrong("succ_a") + gen_anchor_wrong("succ_b")
    run("② 训 succ_a + 等价/锚定错题 → OOD succ_b", tr_c, ood_b)
    run("②' 同上 → OOD succ_a (对照)", tr_c, ood_a)
    # ④ 对称性专用 succ: 加法 succ_a, 乘法 succ_b
    tr_sym = gen_arith("succ_a", "basepoint", hi_mul=0) \
             + [op_sample("succ_b", "basepoint", MUL, m, n, m * n, True)
                for m in range(5) for n in range(5)] \
             + [op_sample("succ_b", "basepoint", MUL, m, n, m * n + 1, False)
                for m in range(5) for n in range(5)]
    ood_sym = gen_ood("succ_a", "basepoint")  # 加法 OOD (succ_a) + 乘法 OOD (succ_b) 各取一半
    ood_sym = [s for s in gen_ood("succ_a", "basepoint") if "multiplication" in "".join([api.name(t) for t in s["seq"]])] \
              + [s for s in gen_ood("succ_b", "basepoint") if "addition" in "".join([api.name(t) for t in s["seq"]])]
    run("④ 对称性专用 succ (加 succ_a/乘 succ_b)", tr_sym, ood_sym)
    print("== 完成 ==", flush=True)
