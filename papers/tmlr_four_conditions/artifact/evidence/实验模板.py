"""template_exp.py — 标准实证实验模板 (方法论 paper_repro/METHODOLOGY.md)

新分析对象 (运算/表示/token 体系) 按本模板跑, 保证可复现可比较.
覆盖: 标准消融 (§1) + 结构直觉对比 (§2) + 对比样本设计 (§3) + 多 seed.

用法:
  from template_exp import run_standard
  run_standard("op_name", chain_fn, seeds=(0,1,2))
  # chain_fn(n) -> 数字 n 的 token 序列 (表示形式)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
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


def init():
    global ZERO, SUCC, ADD, MUL
    ZERO = api.eid_by_name("value_zero")
    SUCC = api.eid_by_name("succ")
    ADD = api.eid_by_name("addition")
    MUL = api.eid_by_name("multiplication")


def default_chain(n):
    """真 numeral (基点 succ 链): 数字 n = succ 应用 n 次于 zero."""
    return [SUCC] * n + [ZERO]


def sample(chain_fn, op, m, n, k, truth):
    """标准判定样本: [is_true][bracket][op][chain m][chain n][bracket][=][chain k][truth]."""
    expr = api.assemble_seq(op, [chain_fn(m), chain_fn(n)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, chain_fn(k)])
    return make_sample(judge_sequence(prop, truth), truth, 2)


def gen_train(chain_fn, add_hi=9, mul_hi=4, hole=None):
    """标准训练: 加法 0..add_hi 全枚举 + 乘法 0..mul_hi (输出链可控).

    hole: 留出 0 组合边界 (k ≥ hole 的 0 侧不训 — 真 OOD 设计, §3).
    """
    out = []
    for m in range(add_hi + 1):
        for n in range(add_hi + 1):
            if hole is not None and (m == 0 or n == 0) and max(m, n) >= hole:
                continue
            k = m + n
            out.append(sample(chain_fn, ADD, m, n, k, True))
            out.append(sample(chain_fn, ADD, m, n, k + 1, False))
    for m in range(mul_hi + 1):
        for n in range(mul_hi + 1):
            k = m * n
            out.append(sample(chain_fn, MUL, m, n, k, True))
            out.append(sample(chain_fn, MUL, m, n, k + 1, False))
    return out


def gen_ood(chain_fn, combos=None, hole=None):
    """标准 OOD: 训练外组合 (两位数加法 + 5..6 乘法) + 0 组合 + 留出组合."""
    if combos is None:
        combos = [(10, 2), (2, 10), (10, 3), (3, 10), (0, 10), (10, 0),
                  (11, 2), (2, 11), (12, 2), (5, 3), (3, 5), (6, 2)]
    out = []
    for m, n in combos:
        for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
            k = f(m, n)
            out.append(sample(chain_fn, op, m, n, k, True))
            out.append(sample(chain_fn, op, m, n, k + 1, False))
    if hole is not None:
        for k in range(hole, 10):          # 留出的 0 组合 (真 OOD)
            for op, f in ((ADD, lambda a, b: a + b), (MUL, lambda a, b: a * b)):
                r = f(0, k)
                out.append(sample(chain_fn, op, 0, k, r, True))
                out.append(sample(chain_fn, op, 0, k, r + 1, False))
                out.append(sample(chain_fn, op, k, 0, r, True))
                out.append(sample(chain_fn, op, k, 0, r + 1, False))
    return out


def evaluate_tok(model, probes, tag):
    """token 级评估 (干净对比, 用户纪律 2026-08-15): 样本全对数 +
    token 对/总数 + 每位置正确率 (崩的形态定位).

    聚合 acc 掩盖崩的位置 — 报告: 多少 token 对/错, 崩在哪个位置.
    """
    rv = rev_vocab()
    batch = collate(probes, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v) for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    per_pos_ok, per_pos_tot = [], []
    samples = []
    for i, s in enumerate(probes):
        L = batch["inputs"].shape[1] - batch["mask"][i].sum().item()
        pred = [rv[p] for p in logits[i, :L].argmax(dim=1).tolist()]
        ok = [p == t for p, t in zip(pred, s["seq"])]
        samples.append((sum(ok), len(ok)))
        while len(per_pos_ok) < len(ok):
            per_pos_ok.append(0); per_pos_tot.append(0)
        for j, o in enumerate(ok):
            per_pos_ok[j] += o; per_pos_tot[j] += 1
    tot_ok = sum(a for a, _ in samples)
    tot = sum(b for _, b in samples)
    print(f"{tag}: 样本全对 {sum(1 for a, b in samples if a == b)}/{len(probes)}"
          f" | token 对 {tot_ok}/{tot} ({tot_ok / tot:.2f})", flush=True)
    print("  位置正确率: " + " ".join(
        f"{per_pos_ok[j]}/{per_pos_tot[j]}" for j in range(min(25, len(per_pos_ok)))), flush=True)
    return samples


def evaluate(model, probes, tag):
    """标准评估: 完整序列逐 token 重建全对 (判定口径)."""
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


def run_standard(label, chain_fn, epochs=60, dim=64, layers=2, seeds=(0, 1, 2),
                 hole=None, combos=None):
    """标准流程: 训练 → OOD (含留出/0 组合) → 多 seed → 伪恢复检查.

    返回: {seed: (train_acc, ood_ok, ood_tot)} — 归档用.
    """
    init()
    tr = gen_train(chain_fn, hole=hole)
    od = gen_ood(chain_fn, combos=combos, hole=hole)
    mx = max(len(s["seq"]) for s in tr + od)
    print(f"== {label}: 训练 {len(tr)} | OOD {len(od)} | 最长 {mx} tokens ==", flush=True)
    results = {}
    for seed in seeds:
        res = train_seq(tr, epochs=epochs, dim=dim, num_layers=layers, seed=seed)
        ok = evaluate(res["model"], od, f"  seed={seed} 训练acc={res['valid_acc']:.3f} OOD")
        results[seed] = (res["valid_acc"], ok, len(od))
    print(flush=True)
    return results


if __name__ == "__main__":
    # 模板自检: 默认真 numeral (succ 链) 标准流程
    run_standard("template 自检 (真 numeral)", default_chain)
