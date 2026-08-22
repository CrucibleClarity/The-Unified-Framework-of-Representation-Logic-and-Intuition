"""ablate_channels.py — 三通道逐项摘除消融 (样本 × 构造 × 箭头), mod 域 (ℤ/7)

通道定义 (inversion 恢复任务, 用户指令 2026-08-15 "挨个摘除消融"):
  A 样本  = neg/reciprocal 对错题 (balanced: 真+假各半) — 数值行为实证
  B 构造  = neg/reciprocal 定义等式 (全真, 只给定义成立实例, 无错题)
  C 箭头  = 元关系样本 (neg ∘ reciprocal = inversion, 模型可见)

mod 域 (ℤ/7, 素数): reciprocal = 乘法逆元 — 非退化!
  整数域缺陷: reciprocal(±1)=±1 恒等 → inversion 与 neg 在 ±1 不可区分,
  探针无法区分真恢复 vs 模式转移 (inversion 当 neg 用).
  mod 域: inversion(2)=3 ≠ neg(2)=5 — 严格区分. 判定 = 完整序列重建.

恢复测试: neg(3)→4 + inversion(2)→3 (复合真值) + inversion(3)→2 (OOD 复合)。
结论判定: 哪个通道 (组合) 决定性; 构造/箭头能否替代样本 (伪恢复用错题排除).
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_all_ops import api, make_sample, gen_samples, numeral_of, eval_any
from lab.judge import judge_sequence
from tokenizer.eval.symmetry_eval import mod_domain
import torch
from train.data import collate, rev_vocab
from train import train_seq

N = 7  # mod 域 (素数, 所有非零元有逆元)

# ---------- 通道样本构造 (全部在 mod 域内) ----------

def samples_chan(op_names=("neg", "reciprocal"), hi=6):
    """A: 对错题 (balanced)"""
    out = []
    with mod_domain(N):
        for op in op_names:
            eid = api.eid_by_name(op)
            try:
                ss, _, _ = gen_samples(eid, hi)
            except Exception:
                continue
            out.extend(ss)
    return out

def construct_chan():
    """B: 定义等式全真样本 — 只给定义成立的真实例, 无错题.

    [is_true][op][bracket][x][bracket][=][result][truth_true]
    mod 域: neg 与 reciprocal 都取 1..N-1 (全非零元, 全有逆元).
    """
    out = []
    with mod_domain(N):
        for op in ("neg", "reciprocal"):
            eid = api.eid_by_name(op)
            for x in range(1, N):
                v = eval_any(eid, [x])
                expr = api.assemble_seq(eid, [numeral_of(x)])
                expr = api.assemble_seq(api.role_token("bracket"), [expr])
                prop = api.assemble_seq(api.role_token("equals"), [expr, numeral_of(v)])
                out.append(make_sample(judge_sequence(prop, True), True, 1))
    return out

def arrow_chan():
    """C: 元关系样本 — 箭头 A:91 可见化 (neg ∘ reciprocal = inversion).

    只声明符号关系, 不给 inversion 任何数值行为.
    """
    out = []
    for a, b in (("neg", "reciprocal"), ("reciprocal", "neg")):
        expr = api.assemble_seq(api.eid_by_name(a), [api.eid_by_name(b)])
        expr = api.assemble_seq(api.role_token("bracket"), [expr])
        prop = api.assemble_seq(api.role_token("equals"), [expr, [api.eid_by_name("inversion")]])
        out.append(make_sample(judge_sequence(prop, True), True, 1))
    return out

# ---------- 恢复测试 (mod 域真值) ----------

def make_probe(op, x, r, truth):
    expr = api.assemble_seq(api.eid_by_name(op), [numeral_of(x)])
    expr = api.assemble_seq(api.role_token("bracket"), [expr])
    prop = api.assemble_seq(api.role_token("equals"), [expr, numeral_of(r)])
    return make_sample(judge_sequence(prop, truth), truth, 1)

def recovery_probes():
    """mod 域 (ℤ/7) 真值: neg(3)=4, inversion(2)=3, inversion(3)=2.

    区分模式转移: inversion(2) 真值 3 ≠ neg(2)=5 — 模型若把 inversion
    当 neg 用 → 探针 2 重建 5 → ✗; 真复合恢复 → 3 → ✓.
    """
    probes = [
        ("neg", 3, 4, True), ("neg", 3, 5, False),
        ("inversion", 2, 3, True), ("inversion", 3, 2, True),
        ("inversion", 2, 5, False),
    ]
    return [make_probe(*p) for p in probes]

def run_ablation(label, with_samples, with_construct, with_arrow, epochs=30, seed=0):
    all_s = []
    if with_samples:
        all_s.extend(samples_chan())
    if with_construct:
        all_s.extend(construct_chan())
    if with_arrow:
        all_s.extend(arrow_chan())
    tag = f"{'样本' if with_samples else '—'}|{'构造' if with_construct else '—'}|{'箭头' if with_arrow else '—'}"
    if not all_s:
        print(f"{label} [{tag}]: 无训练样本 — 恢复 0", flush=True)
        return
    res = train_seq(all_s, epochs=epochs, dim=64, num_layers=2, seed=seed)
    probes = recovery_probes()
    model = res['model']
    batch = collate(probes, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v) for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    rv = rev_vocab()
    results = []
    for i, s in enumerate(probes):
        L = batch["inputs"].shape[1] - batch["mask"][i].sum().item()
        ps = [rv[p] for p in logits[i, :L].argmax(dim=1).tolist()]
        results.append(all(p == t for p, t in zip(ps, s['seq'])))
    n = {0: "neg3", 1: "neg假", 2: "inv2", 3: "inv3", 4: "inv假"}
    det = " ".join(f"{n[i]}={'✓' if r else '✗'}" for i, r in enumerate(results))
    print(f"{label} [{tag}]: {det}  neg {sum(results[:2])}/2  inv {sum(results[2:])}/3  acc={res['valid_acc']:.3f}", flush=True)
    return results

if __name__ == "__main__":
    print("== mod 域 (ℤ/7) 三通道消融矩阵 (全有 → 挨个摘) ==", flush=True)
    run_ablation("① 全有", True, True, True)
    run_ablation("② 摘样本", False, True, True)
    run_ablation("③ 摘构造", True, False, True)
    run_ablation("④ 摘箭头", True, True, False)
    run_ablation("⑤ 只样本", True, False, False)
    run_ablation("⑥ 只构造", False, True, False)
    run_ablation("⑦ 只箭头", False, False, True)
    print("== 完成 ==", flush=True)
