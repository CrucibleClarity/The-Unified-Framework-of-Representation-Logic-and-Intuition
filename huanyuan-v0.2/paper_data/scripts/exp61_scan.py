"""docs/paper_data/scripts/exp61_scan.py —— EXP-61 定义模糊对照扫描

对 exp61_{exact,blur}_e{3,10,40} 各模型测 OOD 判定口径, 记录收敛表.
用法: PYTHONPATH=. python -m docs.paper_data.scripts.exp61_scan --dir <runs_dir>
输出: 定义质量 × epochs 收敛表 + 写入 docs/paper_data/exp61_results.md
"""
import argparse
import glob
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from eval_helpers import load_model, judge_many


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default="archive/log/train")
    args = ap.parse_args()
    print("=== EXP-61: 定义模糊对照 ===")

    rows = []
    for variant in ("exact", "blur"):
        for e in (3, 10, 40):
            matches = sorted(glob.glob(os.path.join(args.dir, f"exp61_{variant}_e{e}_*")))
            if not matches:
                print(f"  {variant} e{e}: 无归档")
                continue
            run = matches[-1]
            model = load_model(run)
            from archive import load_config, load_samples
            from lab import run_exp
            arch = load_config(run)
            exp = arch.get("exp", {})
            cfg = {"synth": {"samples": exp.get("synth", {}).get("samples", [])},
                   "verify": exp.get("verify", {})}
            train_samples = load_samples(run)
            ood = run_exp._make_verify_fn(cfg, train_samples, 0)(12345, [], None)
            a, *_ = judge_many(model, [s["seq"] for s in ood])
            rows.append((variant, e, a, len(ood)))
            print(f"  {variant} e={e}: acc={a:.3f} (n={len(ood)})")

    with open("docs/paper_data/exp61_results.md", "w", encoding="utf-8") as f:
        f.write("# EXP-61 定义模糊对照 (G0/G6 — 语法→训练速度) — 结果记录\n\n")
        f.write("日期: 2026-08-11\n\n## 结果 (定义质量 × epochs 判定口径)\n\n")
        f.write("| 变体 | epochs | 判定口径 |\n|---|---|---|\n")
        for variant, e, a, n in rows:
            f.write(f"| {variant} | {e} | {a:.3f} |\n")
        f.write("\n## 结论\n\n")
        exact = {e: a for v, e, a, _ in rows if v == "exact"}
        blur = {e: a for v, e, a, _ in rows if v == "blur"}
        if exact.get(3, 0) >= 0.9 and blur.get(3, 1) < 0.5:
            f.write("精确组 3 epochs 收敛, 模糊组 3 epochs 不收敛 — "
                    "定义精确 (语法正确) ⇒ 极强训练速度 (SUPPORT).\n")
        elif blur.get(40, 1) < 0.5:
            f.write("模糊组 40 epochs 仍不收敛 — 定义缺失不可通过训练量弥补 "
                    "(定义模糊 = 训练量暴涨, 强 SUPPORT).\n")
        else:
            f.write("结果记录如上 (结论判定需人工核对).\n")


if __name__ == "__main__":
    main()
