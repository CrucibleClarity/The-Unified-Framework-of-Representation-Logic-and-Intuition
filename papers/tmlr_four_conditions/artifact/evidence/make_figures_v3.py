#!/usr/bin/env python3
"""make_figures_v3.py — 四定理 2x2 面板 (极端干净版 v3)

清理项 (对照 v2):
  1. (a) 失败条件红 × 移到数据区真实位置, "never" 短标, 不再溢出
  2. 移除 transAxes 堆叠文字 (condition holds/violated) — 颜色自解释
  3. 数值标签: 0.00 不标 (颜色传达), 值 ≥0.15 白色字标柱内
  4. 标题单行短; y 轴标签单行短
  5. 统一: 所有面板同构两极点 (蓝=恢复/满足, 红=失败), 无网格无边框
"""
import csv
import math
import os
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "..", "..", "..", "结果")

BLUE = "#1a6fb5"
RED = "#c0392b"
GRAY = "#7f7f7f"

plt.rcParams.update({
    "font.size": 11,
    "axes.linewidth": 0.8,
    "xtick.major.size": 3,
    "ytick.major.size": 3,
    "figure.facecolor": "white",
})


def _clean(ax):
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)


def panel_a(ax):
    """T1: decoupling 消融 — 水平条 (peak epoch), 失败条件红 ×."""
    rows = list(csv.DictReader(open(os.path.join(RES, "ablation_summary.tsv")),
                               delimiter="\t"))
    by = defaultdict(list)
    for r in rows:
        if r["group"] == "main":
            by[r["cond"]].append(float(r["peak_epoch"]))
    ok = [("baseline", "baseline"), ("n_align", "n-align"),
          ("decl_full", "decl-full"), ("excl_pollute10", "noise 10%"),
          ("excl_pollute30", "noise 30%"), ("canc_1side", "one-sided"),
          ("canc_partial", "partial")]
    fail = [("layer_dual", "dual-role"), ("no_decl", "no-decl")]
    n_ok, n_fail = len(ok), len(fail)
    for i, (key, lab) in enumerate(ok):
        vals = by[key]
        m = sum(vals) / len(vals)
        sd = math.sqrt(sum((v - m) ** 2 for v in vals) / (len(vals) - 1))
        y = n_ok - 1 - i
        ax.barh(y, m, height=0.62, color=BLUE, alpha=0.92)
        ax.errorbar(m, y, xerr=sd, fmt="none", ecolor=GRAY, capsize=2,
                    linewidth=0.8)
        ax.text(m + 0.5, y, f"{m:.0f}", va="center", ha="left",
                fontsize=9.5, color=BLUE)
    for j, (key, lab) in enumerate(fail):
        y = n_ok + n_fail - 1 - j
        ax.plot(41, y, marker="x", color=RED, markersize=8,
                markeredgewidth=1.8)
        ax.text(42.5, y, "never 1.0", va="center", ha="left",
                fontsize=9, color=RED)
    ylabels = [lab for _, lab in ok] + [lab for _, lab in fail]
    ax.set_yticks(range(n_ok + n_fail))
    ax.set_yticklabels(ylabels, fontsize=9.5)
    ax.set_xlim(10, 52)
    ax.set_ylim(-0.6, n_ok + n_fail - 0.4)
    ax.set_xlabel("peak epoch (per-token OOD = 1.0)", fontsize=10)
    _clean(ax)
    ax.set_title("(a) T1  decoupling ablation", fontsize=11, loc="left", pad=5)


def _poles(ax, pairs, xlabels, title):
    """两极点柱: 蓝=满足 (左), 红=违反 (右). 柱内白字, 零值不标."""
    n = len(pairs)
    w = 0.34
    for i, (lv, rv) in enumerate(pairs):
        if lv >= 0.15:
            ax.bar(i - w / 2, lv, w, color=BLUE, alpha=0.92)
            ax.text(i - w / 2, lv / 2, f"{lv:.2f}", ha="center",
                    va="center", fontsize=9.5, color="white")
        else:
            ax.bar(i - w / 2, lv, w, color=BLUE, alpha=0.92)
        if rv >= 0.15:
            ax.bar(i + w / 2, rv, w, color=RED, alpha=0.92)
            ax.text(i + w / 2, rv / 2, f"{rv:.2f}", ha="center",
                    va="center", fontsize=9.5, color="white")
        else:
            ax.bar(i + w / 2, rv, w, color=RED, alpha=0.92)
            ax.text(i + w / 2, rv + 0.035, "0", ha="center",
                    fontsize=8.5, color=RED)
    ax.set_xticks(range(n))
    ax.set_xticklabels(xlabels, fontsize=9.5)
    ax.set_ylim(0, 1.13)
    ax.set_yticks([0, 0.5, 1.0])
    _clean(ax)
    ax.set_title(title, fontsize=11, loc="left", pad=5)


def panel_b(ax):
    _poles(ax, [(1.0, 0.0)], ["E6  structure vs symbol"],
           "(b) T2  symbol norm")


def panel_c(ax):
    _poles(ax, [(1.0, 0.0), (1.0, 0.5)],
           ["E12  translatability", "E13/16  conflict"],
           "(c) T3  presentation legality")


def panel_d(ax):
    _poles(ax, [(1.0, 0.0), (1.0, 0.0)],
           ["E12  two-pole", "E15  strict transfer"],
           "(d) T4  intuition precision")


def main():
    fig, axes = plt.subplots(2, 2, figsize=(10.5, 7.2))
    panel_a(axes[0][0])
    panel_b(axes[0][1])
    panel_c(axes[1][0])
    panel_d(axes[1][1])
    fig.tight_layout(w_pad=3.4, h_pad=2.4)
    fig.savefig(os.path.join(HERE, "fig_theorems.png"), dpi=250)
    print("fig_theorems.png (v3)")


if __name__ == "__main__":
    main()
