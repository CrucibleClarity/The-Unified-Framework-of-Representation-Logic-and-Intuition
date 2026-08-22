"""axis_succ_exp.py — 不同轴的 succ + 单轴消融 (用户指令 2026-08-15)

问题 1: 不同轴的 succ — 多轴系统中每轴有独立后继概念 (succ_0/succ_1).
问题 2: 每轴单独 succ 是否可消融 — 摘除一轴的训练样本 (零样本),
        测跨轴迁移 (从轴 0 学到的规则能否用于轴 1).

设计:
  注入 succ_0 (轴 0 后继), succ_1 (轴 1 后继) — 独立概念 token
  数字 (轴 a, n) = succ_a^n(zero); 加法 = 轴内链拼接
  组 A: 双轴都训 (轴 0 + 轴 1 加法样本) — 基线
  组 B: 只训轴 0 (轴 1 零样本) — OOD: 轴 1 加法 (跨轴迁移) + 轴 0 加法 (同轴外推)
  组 C: 只训轴 1 — 对称
每组 3 seeds, 完整序列重建判定.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
from gen_all_ops import api, make_sample
from lab.judge import judge_sequence
from lab.synth_core import inject_dual_tokens
import torch
from train.data import collate, rev_vocab
from train import train_seq

ZERO = None
ADD = None
SUCC_AX = {}


def init():
    global ZERO, ADD, SUCC_AX
    ZERO = api.eid_by_name("value_zero")
    ADD = api.eid_by_name("addition")
    inject_dual_tokens({
        f"succ_axis_{a}": {"form": "explicit", "arrange": "application",
                           "rules": [{"term": ["D:194"]}], "references": ["D:194"]}
        for a in (0, 1)})
    for a in (0, 1):
        SUCC_AX[a] = api.eid_by_name(f"succ_axis_{a}")


def chain(axis, n):
    return [SUCC_AX[axis]] * n + [ZERO]


def add_sample(axis, m, n, truth):
    expr = api.assemble_seq(ADD, [chain(axis, m), chain(axis, n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain(axis, m + n)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train_axis(axis, hi=9):
    out = []
    for m in range(hi + 1):
        for n in range(hi + 1):
            out.append(add_sample(axis, m, n, True))
            out.append(add_sample(axis, m, n + 1, False))
    return out


def gen_ood_axis(axis):
    """OOD: 训练外数字组合 (10..12) 在该轴上."""
    out = []
    for m, n in ((10, 2), (2, 10), (10, 3), (3, 10), (11, 2), (12, 2)):
        out.append(add_sample(axis, m, n, True))
        out.append(add_sample(axis, m, n + 1, False))
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
    ood0 = gen_ood_axis(0)
    ood1 = gen_ood_axis(1)
    print(f"轴 0 OOD {len(ood0)} | 轴 1 OOD {len(ood1)}", flush=True)
    print("== A 双轴都训 (基线) ==", flush=True)
    for seed in (0, 1, 2):
        tr = gen_train_axis(0) + gen_train_axis(1)
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], ood0, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 轴0OOD")
        evaluate(res["model"], ood1, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 轴1OOD")
    print("== B 只训轴 0 (轴 1 零样本 — 单轴消融) ==", flush=True)
    for seed in (0, 1, 2):
        tr = gen_train_axis(0)
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], ood0, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 轴0OOD(同轴外推)")
        evaluate(res["model"], ood1, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 轴1OOD(跨轴迁移)")
    print("== C 只训轴 1 (对称) ==", flush=True)
    for seed in (0, 1, 2):
        tr = gen_train_axis(1)
        res = train_seq(tr, epochs=60, dim=64, num_layers=2, seed=seed)
        evaluate(res["model"], ood0, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 轴0OOD(跨轴迁移)")
        evaluate(res["model"], ood1, f"  seed={seed} 训练acc={res['valid_acc']:.3f} 轴1OOD(同轴外推)")
    print("== 完成 ==", flush=True)
