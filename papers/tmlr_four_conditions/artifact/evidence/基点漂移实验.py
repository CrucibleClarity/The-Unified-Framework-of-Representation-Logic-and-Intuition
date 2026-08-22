"""basepoint_drift_exp.py — 基点漂移对比 (用户指令 2026-08-15)

用户: 链底选择不是问题, 关键是基点漂移; value_zero 应从 basepoint 派生.

真 numeral: 数字 n 锚在基点 e = succ^n(e). 基点漂移 = 参考系变换
(穿折越 T_{e→f}(x) = x + (f−e)).

4 组对比 (加乘 0..9 + 0..4, OOD 训练外数字 10+):
  ① 同基点: 训锚 basepoint, OOD 同锚外推 — 基线
  ② 跨基点零样本: 训锚 basepoint, OOD 锚 basepoint_f — 漂移零样本
  ③ 双锚训练: 训锚 basepoint + 锚 basepoint_f, OOD 双锚外推
  ④ 漂移显式桥接: 训锚 basepoint 加乘 + 漂移样本 T_{0→f}(n)=n_f,
     OOD 锚 basepoint_f 加乘 — 显式漂移能否桥接
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import inject_dual_tokens
import torch
from train.data import collate, rev_vocab
from train import train_seq

SUCC = None
ADD = None
MUL = None
BP0 = None
BPF = None


def init():
    global SUCC, ADD, MUL, BP0, BPF
    SUCC = api.eid_by_name("succ")
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")
    BP0 = api.eid_by_name("basepoint")
    inject_dual_tokens({"basepoint_f": {"form": "axiomatic", "arrange": "atom",
                                         "references": []}})
    BPF = api.eid_by_name("basepoint_f")


def chain(bp, n):
    return [SUCC] * n + [bp]


def op_sample(bp, op, m, n, k, truth):
    expr = api.assemble_seq(op, [chain(bp, m), chain(bp, n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(bp, k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def drift_sample(n):
    """穿折越 T_{0→f}: 锚 0 的数字 n → 锚 f 的数字 n (基点漂移)."""
    expr = api.assemble_seq(api.eid_by_name("basepoint_move"),
                            [chain(BP0, n)]) if False else None
    # 漂移 = 等价声明: 锚 0 的 n ≡ 锚 f 的 n (同一数值不同锚)
    prop = api.assemble_seq(api.role_token("equals"), [chain(BP0, n), chain(BPF, n)])
    return make_sample(judge_sequence(prop, True), True, 1)


def gen_arith(bp, hi_add=9, hi_mul=4):
    out = []
    for m in range(hi_add + 1):
        for n in range(hi_add + 1):
            k = m + n
            out.append(op_sample(bp, ADD, m, n, k, True))
            out.append(op_sample(bp, ADD, m, n, k + 1, False))
    for m in range(hi_mul + 1):
        for n in range(hi_mul + 1):
            k = m * n
            out.append(op_sample(bp, MUL, m, n, k, True))
            out.append(op_sample(bp, MUL, m, n, k + 1, False))
    return out


def gen_ood(bp):
    out = []
    for m, n in ((10, 2), (2, 10), (10, 3), (3, 10), (11, 2), (12, 2), (5, 3), (6, 2)):
        for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
            k = f(m, n)
            out.append(op_sample(bp, op, m, n, k, True))
            out.append(op_sample(bp, op, m, n, k + 1, False))
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
    ood0 = gen_ood(BP0)
    oodf = gen_ood(BPF)
    print(f"同锚 OOD {len(ood0)} | 漂移锚 OOD {len(oodf)}", flush=True)
    print("== ① 同基点 (锚 basepoint, 基线) ==", flush=True)
    for seed in (0, 1, 2):
        res = train_seq(gen_arith(BP0), epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], ood0, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 同锚OOD")
    print("== ② 跨基点零样本 (训锚0, OOD 锚f — 漂移) ==", flush=True)
    for seed in (0, 1, 2):
        res = train_seq(gen_arith(BP0), epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], oodf, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 漂移OOD")
    print("== ③ 双锚训练 (锚0 + 锚f) ==", flush=True)
    for seed in (0, 1, 2):
        tr = gen_arith(BP0) + gen_arith(BPF)
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], ood0, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 锚0OOD")
        evaluate(res["model"], oodf, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 锚fOOD")
    print("== ④ 漂移显式桥接 (锚0加乘 + 漂移等价样本, OOD 锚f) ==", flush=True)
    for seed in (0, 1, 2):
        tr = gen_arith(BP0) + [drift_sample(n) for n in range(10)]
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], oodf, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 漂移OOD")
    print("== 完成 ==", flush=True)
