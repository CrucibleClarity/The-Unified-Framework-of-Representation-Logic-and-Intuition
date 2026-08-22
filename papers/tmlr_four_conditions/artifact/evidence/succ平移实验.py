"""succ_shift_exp.py — succ 平移不变性 + value_zero 错题 (用户指令 2026-08-15)

问题 3 (最深刻): "0 后继 1 的 succ 和 1 后继 2 的 succ 是否是同一个?"
  = 后继的平移不变性: succ 在链上每步是否同一规则.
  实验: 只训 succ(0)=1 (1 个真样本), OOD 测 succ(1)=2..succ(7)=8.
  外推成功 → 0→1 与 1→2 是同一个 succ (同一规则, 平移不变);
  外推失败 → 每步 succ 需分别学 (非同一).
  对比: 训 succ(0..k) 不同范围, 看外推率随训练覆盖的变化.

问题 4: value_zero 需要错题 — 0 的表示必须有负例 (succ(0)≠0,
  0≠1). 变体: 训练含/不含 0 错题, 测 OOD 差异.

真 numeral: chain(n) = [succ]×n + [zero]; 判定 = 完整序列重建.
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


def init():
    global ZERO, SUCC
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")


def chain(n):
    return [SUCC] * n + [ZERO]


def succ_sample(n, truth):
    """succ 判定: [is_true][bracket][succ][chain(n)][bracket][=][chain(n+1)][truth]."""
    expr = api.assemble_seq(SUCC, [chain(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(n + 1)])
    return make_sample(judge_sequence(prop, truth), truth, 1)


def zero_wrong_samples():
    """value_zero 错题: succ(0) ≠ 0 (1≠0), 0 ≠ 1, 0 ≠ 2."""
    out = []
    # succ(0) = 0 是假 (0 的后继不是 0)
    expr = api.assemble_seq(SUCC, [chain(0)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(0)])
    out.append(make_sample(judge_sequence(prop, False), False, 1))
    # 0 ≠ 1, 0 ≠ 2 (数字表示比较)
    for k in (1, 2):
        prop = api.assemble_seq(api.role_token("equals"), [chain(0), chain(k)])
        out.append(make_sample(judge_sequence(prop, False), False, 1))
    return out


def gen_train(hi, with_zero_wrong):
    """训 succ(0..hi) 真 + 错题 (succ(n) ≠ n)."""
    out = []
    for n in range(hi + 1):
        out.append(succ_sample(n, True))
        # 错题: succ(n) = n (原地不动是假)
        expr = api.assemble_seq(SUCC, [chain(n)])
        expr = api.assemble_seq(api.role_token("bracket"), [expr])
        prop = api.assemble_seq(api.role_token("equals"), [expr, chain(n)])
        out.append(make_sample(judge_sequence(prop, False), False, 1))
    if with_zero_wrong:
        out.extend(zero_wrong_samples())
    return out


def gen_ood(his=(1, 2, 3, 4, 5, 6, 7)):
    """OOD: succ(n)=n+1 (训练外 n)."""
    out = []
    for n in his:
        out.append(succ_sample(n, True))
        out.append(succ_sample(n, False))
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
    ood = gen_ood()
    print(f"OOD {len(ood)} 条 (succ(1..7), 训练外 n)", flush=True)
    for hi, label in ((0, "只训 succ(0)=1"), (1, "训 succ(0..1)"),
                      (2, "训 succ(0..2)"), (4, "训 succ(0..4)")):
        for zw in (False, True):
            tr = gen_train(hi, zw)
            tag = f"{label} {'+0错题' if zw else '无0错题'}"
            print(f"== {tag} (训练 {len(tr)}) ==", flush=True)
            for seed in (0, 1, 2):
                res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
                evaluate(res["model"], ood, f"  seed={seed} 训练acc={res['valid_acc']:.3f} succOOD")
        print(flush=True)
    print("== 完成 ==", flush=True)
