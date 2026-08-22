"""lab/gen_all_ops.py —— 通用元数样本生成 + 训练 (全部 19 个运算 token)

沿定义 signature 元数分发 (零硬编码元数): 一元/二元/三元/四元全枚举.
序列组装沿 gtoken/ptoken (judge_sequence/nested_seq 复用).
"""
from __future__ import annotations

import os
import sys
import json
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from tokenizer import api
from lab.synth_core import balanced_samples, make_sample, numeral_of
from lab.judge import judge_sequence

OPS = ["fold", "unfold", "modulo", "ring_addition", "basepoint_move", "teleport",
       "involution", "orthogonal", "self_inverse_gate", "hadamard", "cnot",
       "toffoli", "qft", "period_axis", "measure", "time_reversal", "summon",
       "flip", "storage_is_computation", "midpoint", "relpos"]


def arity_of(eid: str) -> int:
    """元数: 沿定义 signature params 长度 (知识在 token 数据)."""
    from repo_v5.tokenizer.maintain import core
    sig = core.load_all()[eid]["definition"].get("signature")
    return len(sig["params"]) if sig else 2


def eval_any(eid, args):
    """任意元数求值 (api.eval_op, numeral token 往返)."""
    from lab.synth_core import _numeral_value_of
    toks = [numeral_of(a) for a in args]
    return _numeral_value_of(api.eval_op(eid, toks))


MASK_OP = None  # 屏蔽实验: 设 "relpos" 时, 该运算输入 a→0 (真值用真 a)


def gen_samples(eid: str, hi: int, neg_mode: int = 1) -> tuple:
    """沿元数枚举全组合: 每组合 1 真 + neg_mode 个错题."""
    arity = arity_of(eid)
    if arity == 2:
        return balanced_samples(max_depth=2, hi=hi, op=eid, neg_mode=neg_mode)
    samples, npos, nneg = [], 0, 0
    if arity == 1:
        combos = list(range(hi + 1))                       # 一元: 枚举 x
    elif arity == 3:
        combos = product(range(hi + 1), repeat=3)          # 三元: 枚举 (a,b,c)
    else:  # 4
        combos = product(range(hi + 1), range(4), range(4), range(4))  # x,c1,c2,t
    for combo in combos:
        args = [combo] if arity == 1 else list(combo)
        masked = False
        if MASK_OP is not None and api.name(eid) == MASK_OP and len(args) >= 2:
            masked = True            # 输入屏蔽 a (值→0), 真值仍用真 a
        args_in = [0 if masked else args[0]] + args[1:] if masked else args
        try:
            result = eval_any(eid, args)
        except (ValueError, IndexError):
            continue
        # 序列: [judge][括号][a][op][b]...[括号][=][result][truth] (输入用屏蔽值)
        expr = numeral_of(args_in[0])
        for a in args_in[1:]:
            expr = api.assemble_seq(eid, [expr, numeral_of(a)])
            expr = api.assemble_seq(api.role_token("bracket"), [expr])
        prop = api.assemble_seq(api.role_token("equals"), [expr, numeral_of(result)])
        samples.append(make_sample(judge_sequence(prop, True), True, arity))
        npos += 1
        for bad in range(result + 1, result + 1 + neg_mode):
            prop_bad = api.assemble_seq(api.role_token("equals"),
                                        [expr, numeral_of(bad)])
            samples.append(make_sample(judge_sequence(prop_bad, False), False, arity))
            nneg += 1
    return samples, npos, nneg


def gen_ood(eid: str, arity: int, n: int = 30, seed: int = 1) -> list:
    """OOD 样本: 随机参数 (训练范围外分布), 每运算 n 个真题."""
    import random
    rng = random.Random(seed)
    samples = []
    while len(samples) < n:
        if arity == 1:
            args = [rng.randint(0, 50)]
        elif arity == 2:
            args = [rng.randint(0, 20), rng.randint(2, 15)]
        elif arity == 3:
            args = [rng.randint(0, 20), rng.randint(0, 5), rng.randint(2, 15)]
        else:
            args = [rng.randint(0, 20), rng.randint(0, 4), rng.randint(0, 4), rng.randint(0, 4)]
        masked = False
        if MASK_OP is not None and api.name(eid) == MASK_OP and len(args) >= 2:
            masked = True
        args_in = [0 if masked else args[0]] + args[1:] if masked else args
        try:
            result = eval_any(eid, args)
        except (ValueError, IndexError):
            continue
        expr = numeral_of(args_in[0])
        for a in args_in[1:]:
            expr = api.assemble_seq(eid, [expr, numeral_of(a)])
            expr = api.assemble_seq(api.role_token("bracket"), [expr])
        prop = api.assemble_seq(api.role_token("equals"), [expr, numeral_of(result)])
        samples.append(make_sample(judge_sequence(prop, True), True, arity))
    return samples


def ood_acc_fn(model, ood_samples_all):
    """OOD 判定 acc: 完整序列逐 token 全对率 (同 run_exp 判定口径)."""
    import torch
    from train.data import collate, rev_vocab
    if not ood_samples_all:
        return 0.0
    batch = collate(ood_samples_all, input_mode="ids")
    dev = next(model.parameters()).device
    batch = {k: (v.to(dev) if isinstance(v, torch.Tensor) else v)
             for k, v in batch.items()}
    model.eval()
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    B, L = logits.shape[0], logits.shape[1]
    real_lens = L - batch["mask"].sum(dim=1)
    pred_idx = logits.argmax(dim=2)
    rv = rev_vocab()
    hit = 0
    for i, s in enumerate(ood_samples_all):
        rl = real_lens[i].item()
        preds = [rv[p] for p in pred_idx[i, :rl].tolist()]
        if all(p == t for p, t in zip(preds, s["seq"])):
            hit += 1
    return hit / len(ood_samples_all)


def main():
    all_s, total_p, total_n = [], 0, 0
    ood_all = []
    for op in OPS:
        eid = api.eid_by_name(op)
        arity = arity_of(eid)
        hi = 9 if arity <= 2 else (5 if arity == 3 else 5)
        try:
            ss, p, n = gen_samples(eid, hi)
        except Exception as e:
            print(f"  {op:24} 跳过: {type(e).__name__}: {str(e)[:50]}")
            continue
        all_s.extend(ss)
        total_p += p
        total_n += n
        ood_all.extend(gen_ood(eid, arity))
        print(f"  {op:24} 元数={arity} 真={p:4d} 假={n:4d} 共={len(ss):5d}")
    print(f"总计: 真 {total_p} / 假 {total_n} / 共 {len(all_s)} | OOD: {len(ood_all)}")
    # 训练 (混合全运算, 逐 epoch OOD 曲线)
    from train import train_seq
    res = train_seq(all_s, epochs=30, dim=64, num_layers=2, seed=0,
                    epoch_eval_fn=lambda m: ood_acc_fn(m, ood_all))
    print(f"train acc={res['acc']:.3f} valid_acc={res['valid_acc']:.3f}")
    print(f"OOD 逐 epoch: {' '.join(f'{x:.3f}' for x in res['epoch_gen'])}")
    json.dump({"samples": len(all_s), "npos": total_p, "nneg": total_n,
               "losses": res["losses"], "acc": res["acc"],
               "ood_curve": res["epoch_gen"]},
              open("/tmp/all_ops_train.json", "w"), indent=1)


if __name__ == "__main__":
    main()
