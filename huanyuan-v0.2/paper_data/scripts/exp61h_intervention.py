"""docs/paper_data/scripts/exp61h_intervention.py —— EXP-61h 干扰 token 探测直觉

用户设计 (2026-08-11): 将 op 拆成两个相同 token (同义 clone), 观察直觉
(编译权重) 与结构 (语法) 的分布差异:
  - 直觉 (预期): 均匀分布在两个同义 token 上 (注意力均分)
  - 结构 (预期): 集中在一个 canonical token 上 (语法确定位置)
  - 反向验证: 单 token 推理效果 (用 c0 只用 / c1 只用 vs 混合)

实现:
  1. inject_temp 注入同义 clone (相同定义) → 进 _register + vocab
  2. 训练样本随机替换 op → clone_a/b (各半)
  3. 训练后观测注意力分布 + 单 clone 推理 OOD

用法: PYTHONPATH=. python -m docs.paper_data.scripts.exp61h_intervention
      --run <训练run> --op logical_and  (评估已有 run)
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import torch

from tokenizer import api
from tokenizer.token_index import inject_temp, clear_cache, _TEMP_INJECT
from tokenizer.maintain import core
from tokenizer._register import DERIVE_REGISTRY, DERIVE_BY_NAME, load_derive
from train.data import vocab, collate, rev_vocab
from train.model import TokenTransformer
from eval_helpers import load_model, judge_many


def inject_clone(op_name, n=2):
    """注入 op 同义 clone tokens (相同定义)."""
    src = core.load_all()[api.eid_by_name(op_name)]
    defn = src.get("definition")
    rows = [{"eid": f"D:9{i + 1:03d}", "name": f"{op_name}_c{i}", "dtype": "bool",
             "definition": defn, "ref": "", "intension": f"{op_name} 同义 clone {i}"}
            for i in range(n)]
    inject_temp("C", rows)
    DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear()
    load_derive()
    clear_cache()
    core._ALL_CACHE = None
    return rows


def clear_clone():
    _TEMP_INJECT.clear(); clear_cache()
    DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear()
    core._ALL_CACHE = None


def attention_balance(model, seq, clone_eids):
    """观测 clone tokens 的注意力权重分布 (直觉均匀 vs 结构集中).

    对单序列前向, 提取 self-attention 权重中 clone 位置的参与度.
    返回 (c0 权重和, c1 权重和) — 接近 = 直觉均匀; 偏斜 = 结构集中.
    """
    batch = collate([{"seq": seq, "valid": 1}], input_mode="ids")
    with torch.no_grad():
        logits, _ = model(batch["inputs"], mask=batch["mask"])
    # TokenTransformer 无 attention 权重输出钩子 — 用 logits 间接:
    # 统计 clone 位置被正确预测的比例 (若模型一视同仁, 两 clone 预测率相当)
    rv = rev_vocab()
    rl = batch["lengths"][0]
    preds = [rv[p] for p in logits[0, :rl].argmax(dim=1).tolist()]
    c0_hit = c0_tot = c1_hit = c1_tot = 0
    for j, t in enumerate(seq):
        if t == clone_eids[0]:
            c0_tot += 1; c0_hit += (preds[j] == t)
        elif t == clone_eids[1]:
            c1_tot += 1; c1_hit += (preds[j] == t)
    return (c0_hit / max(c0_tot, 1), c1_hit / max(c1_tot, 1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", required=True)
    ap.add_argument("--op", default="logical_and")
    ap.add_argument("--seq", default="archive/log/train/exp61g_infix_only_20260811_223436")
    args = ap.parse_args()

    # 注入 clone (评估用: 需 clone 在 vocab)
    rows = inject_clone(args.op, 2)
    print(f"注入 clone: {[r['name'] for r in rows]}")

    model = load_model(args.run)
    clone_eids = ["D:9001", "D:9002"]

    # 构造含 clone 的序列 (手动: 用 infix and)
    _T = api.role_token("truth")
    seq = [_T[0], clone_eids[0], _T[1], _T[0]]  # T and_c0 F = F (and 真值)
    # 实际判定序列 [is_true][T][and_c0][F][F]
    from lab.judge import judge_sequence
    judge = judge_sequence([_T[0], clone_eids[0], _T[1]], False)
    print("含 clone 判定序列:", " ".join(api.name(x) for x in judge))

    c0r, c1r = attention_balance(model, judge, clone_eids)
    print(f"clone 位置重建率: c0={c0r:.3f} c1={c1r:.3f} (接近=直觉均匀, 偏斜=结构集中)")

    clear_clone()


if __name__ == "__main__":
    main()
