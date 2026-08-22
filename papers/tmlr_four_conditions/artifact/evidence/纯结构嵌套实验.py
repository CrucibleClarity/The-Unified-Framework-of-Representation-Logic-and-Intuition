"""succ_nest_exp.py — 纯结构嵌套定义实验 (用户指令 2026-08-15)

无符号 token (零 S 层参与), 无基点漂移 (零位置-值/numeral 结构):
  数字 n = succ 嵌套应用 n 次于 zero (succ^n zero — 纯结构, 无记法)
  加法/乘法 = 结构嵌套判定: 2+2 2×2 的嵌套定义一起训练
  含 0 的加法和乘法全枚举 (0+m, m+0, 0×m, m×0, 0+0, 0×0)
测收敛: 训练 acc 曲线 + OOD (训练外数字的结构外推).

序列形式 (应用平铺, 与 gen_samples 一致):
  [is_true][bracket][op][succ^m zero][succ^n zero][bracket][equals][succ^k zero][truth]
真值: m+n=k (加) / m×n=k (乘); 错题: k = m+n+1 等.
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
ADD = None
MUL = None


def _tokens():
    global ZERO, SUCC, ADD, MUL
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")


def chain(n):
    """数字 n 的纯结构表示: succ 嵌套应用 n 次于 zero (succ^n zero)."""
    return [SUCC] * n + [ZERO]


def op_sample(op, m, n, k, truth):
    """结构嵌套判定样本: op(succ^m 0, succ^n 0) = succ^k 0 真/假."""
    expr = api.assemble_seq(op, [chain(m), chain(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train(hi=4, neg=1):
    """0..hi 全组合 (含 0 的加减/乘除全枚举): 每真 + neg 个错题."""
    out = []
    for m in range(hi + 1):
        for n in range(hi + 1):
            for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
                k = f(m, n)
                out.append(op_sample(op, m, n, k, True))
                for d in range(1, neg + 1):
                    out.append(op_sample(op, m, n, k + d, False))
    return out


def gen_ood(his=(5, 6, 7)):
    """OOD: 训练外数字的结构外推, 含 0 组合 (0+5 5+0 0×5 5×0)."""
    out = []
    for hi in his:
        for m, n in ((hi, hi), (3, hi), (hi, 2), (0, hi), (hi, 0)):
            for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
                k = f(m, n)
                out.append(op_sample(op, m, n, k, True))
                out.append(op_sample(op, m, n, k + 1, False))
    return out


def evaluate(model, probes, tag):
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
    print(f"{tag}: {ok}/{len(probes)}", flush=True)
    return ok / len(probes)


if __name__ == "__main__":
    _tokens()
    train_s = gen_train()
    ood_s = gen_ood()
    print(f"训练 {len(train_s)} 样本 (0..4 加乘, 含 0 全枚举) | OOD {len(ood_s)} 条", flush=True)
    print("样例:", " ".join(api.name(t) for t in train_s[0]["seq"]), flush=True)
    res = train_seq(train_s, epochs=60, dim=64, num_layers=2, seed=0)
    print(f"训练收敛: acc={res['valid_acc']:.3f}", flush=True)
    evaluate(res["model"], ood_s, "OOD 结构外推")
    print("== 完成 ==", flush=True)
