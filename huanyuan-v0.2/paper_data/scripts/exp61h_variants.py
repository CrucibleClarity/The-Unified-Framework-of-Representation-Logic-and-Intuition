"""docs/paper_data/scripts/exp61h_variants.py —— EXP-61h 变体矩阵

用户要求的变体 (logical_and 干扰 token):
  V2same:  2 个相同 token (c0=c1=and)          — canonical 化?
  V3same:  3 个相同 token (c0=c1=c2=and)       — 拆越多语法越乱?
  V2diff:  2 个不同 token (c0=and, c1=or)       — 语义不同分配
  V3diff:  3 个不同 token (c0=and, c1=or, c2=xor) — 全不同
  V3mix:   3 token, 2 同 1 异 (c0=c1=and, c2=or) — 混合
  位置尝试: 每个 token 在每个 op 位置单独推理

用法: PYTHONPATH=. python -m docs.paper_data.scripts.exp61h_variants --variant <V2same|V3same|V2diff|V3diff|V3mix>
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
from train import train_seq
from train.data import vocab
from lab import run_exp
from lab.judge import judge_sequence


def inject_multi(defs_by_name):
    """注入多个 (可能不同语义) 的 token. defs_by_name: {name: (dtype, definition)}."""
    rows = []
    for i, (name, (dtype, defn)) in enumerate(defs_by_name.items()):
        rows.append({"eid": f"D:9{i + 1:03d}", "name": name, "dtype": dtype,
                     "definition": defn, "ref": "", "intension": f"{name}"})
    inject_temp("C", rows)
    DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear(); load_derive()
    clear_cache(); core._ALL_CACHE = None
    return rows


def get_def(op_name):
    return core.load_all()[api.eid_by_name(op_name)].get("definition")


def build_train_replace(op_name, token_names):
    """构建训练样本 + 轮换替换 op → token_names (均匀)."""
    from lab import synth_core
    cfg = json.load(open("docs/paper_data/configs/exp61g_infix_only.json"))
    train, _, _ = synth_core.compose_samples(samples=cfg["synth"]["samples"], seed=0)
    op_eid = api.eid_by_name(op_name)
    positions = [(si, i) for si, s in enumerate(train)
                 for i, e in enumerate(s["seq"]) if e == op_eid]
    cnt = [0] * len(token_names)
    for k, (si, i) in enumerate(positions):
        tok = token_names[k % len(token_names)]
        train[si]["seq"][i] = tok
        cnt[k % len(token_names)] += 1
    return train, cnt


def judge_all(model, seqs):
    ss = [{"seq": s, "valid": 1} for s in seqs]
    if len(ss) < 2:
        ss = ss + [{"seq": seqs[0], "valid": 1}]
    return run_exp._judge_eval(model, ss)[0]


def eval_single_tokens(model, eids, op_semantics):
    """每个 token 单独推理 (全部位置)."""
    _T = api.role_token("truth"); T, F = _T
    res = {}
    for eid, sem in zip(eids, op_semantics):
        seqs = []
        for a in (True, False):
            for b in (True, False):
                # op 在 arg0 后 (中缀), 也用前缀 (arg0 前)
                infix = judge_sequence([T if a else F, eid, T if b else F], sem(a, b))
                prefix = judge_sequence([eid, T if a else F, T if b else F], sem(a, b))
                seqs += [infix, prefix]
        res[eid] = judge_all(model, seqs)
    return res


VARIANTS = {
    # (name, {token_name: (dtype, defn)})
    "V2same": lambda: {"logical_and_c0": ("bool", get_def("logical_and")),
                       "logical_and_c1": ("bool", get_def("logical_and"))},
    "V3same": lambda: {"logical_and_c0": ("bool", get_def("logical_and")),
                       "logical_and_c1": ("bool", get_def("logical_and")),
                       "logical_and_c2": ("bool", get_def("logical_and"))},
    "V2diff": lambda: {"logical_and_c0": ("bool", get_def("logical_and")),
                       "logical_or_c1": ("bool", get_def("logical_or"))},
    "V3diff": lambda: {"logical_and_c0": ("bool", get_def("logical_and")),
                       "logical_or_c1": ("bool", get_def("logical_or")),
                       "logical_xor_c2": ("bool", get_def("logical_xor"))},
    "V3mix": lambda: {"logical_and_c0": ("bool", get_def("logical_and")),
                      "logical_and_c1": ("bool", get_def("logical_and")),
                      "logical_or_c2": ("bool", get_def("logical_or"))},
}

SEM = {
    "logical_and": lambda a, b: a and b,
    "logical_or": lambda a, b: a or b,
    "logical_xor": lambda a, b: a != b,
}


def main(variant, epochs=15):
    defs = VARIANTS[variant]()
    rows = inject_multi(defs)
    eids = [r["eid"] for r in rows]
    names = [r["name"] for r in rows]
    print(f"[{variant}] 注入: {names}, vocab={len(vocab())}")

    train, cnt = build_train_replace("logical_and", eids)
    print(f"替换分布: {dict(zip(names, cnt))}")

    res = train_seq(train, epochs=epochs, dim=64, num_layers=2, seed=0,
                    token=f"exp61h_{variant}")
    model = res["model"]
    print(f"train acc={res['acc']:.3f} 归档={res.get('run_dir')}")

    sem = [SEM[n.split("_c")[0]] for n in names]
    eval_res = eval_single_tokens(model, eids, sem)
    print(f"单 token 推理 (全部位置):")
    for n, e in zip(names, eids):
        print(f"  {n}: {eval_res[e]:.3f}")
    print("结论: 全部≈1.0 → 均匀/多语义都保留; 单一1.0其余0 → 集中")

    _TEMP_INJECT.clear(); clear_cache(); DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear()


def main_position_scan():
    """用户要求: 拆成 3 个 token (2 同 1 异), 不同 token 每个位置都尝试一次.

    变体: logical_and_c0/c1 (同义), logical_or_c2 (异义)
    位置扫描: 干扰 token (c2) 出现在序列不同位置时, 模型归因如何变化.
    当前 V3mix 已测 (c2 混合位置 → 0.25); 本函数测 c2 单独在各位置.
    """
    import json as _json
    from tokenizer import api as _api
    from tokenizer.token_index import inject_temp, clear_cache, _TEMP_INJECT
    from tokenizer.maintain import core
    from tokenizer._register import DERIVE_REGISTRY, DERIVE_BY_NAME, load_derive
    from train import train_seq
    from train.data import vocab
    from lab import run_exp
    from lab.judge import judge_sequence

    defs = VARIANTS["V3mix"]()
    rows = inject_multi(defs)
    eids = [r["eid"] for r in rows]
    names = [r["name"] for r in rows]
    train, cnt = build_train_replace("logical_and", eids)
    res = train_seq(train, epochs=15, dim=64, num_layers=2, seed=0, token="exp61h_posscan")
    model = res["model"]
    print(f"[位置扫描] train acc={res['acc']:.3f}")

    _T = _api.role_token("truth"); T, F = _T
    c0, c1, c2 = eids
    # c2 在每个位置单独推理 (作为 and 语义): 位置 = [A][op][B] 的 op, [op][A][B], [A][B][op]
    def mk_pos(op, pos, a, b, truth):
        aa = T if a else F; bb = T if b else F
        if pos == 0: return judge_sequence([op, aa, bb], truth)
        if pos == 1: return judge_sequence([aa, op, bb], truth)
        return judge_sequence([aa, bb, op], truth)
    def judge(seqs):
        ss = [{"seq": s, "valid": 1} for s in seqs]
        if len(ss) < 2: ss = ss + [{"seq": seqs[0], "valid": 1}]
        return run_exp._judge_eval(model, ss)[0]
    for name, eid in zip(names, eids):
        for pos in (0, 1, 2):
            seqs = [mk_pos(eid, pos, a, b, a and b) for a in (True,False) for b in (True,False)]
            print(f"  {name} @pos{pos}: {judge(seqs):.3f}")
    _TEMP_INJECT.clear(); clear_cache(); DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear()


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--variant", choices=list(VARIANTS))
    ap.add_argument("--epochs", type=int, default=15)
    ap.add_argument("--position-scan", action="store_true")
    args = ap.parse_args()
    if args.position_scan:
        main_position_scan()
    elif args.variant:
        main(args.variant, args.epochs)
    else:
        ap.error("需要 --variant 或 --position-scan")
