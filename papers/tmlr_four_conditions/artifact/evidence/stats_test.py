#!/usr/bin/env python3
"""stats_test.py — 消融峰值 epoch 的统计检验 (无 scipy 依赖)

对每个条件 vs baseline 做:
  1) Welch t-test (不等方差)
  2) Mann-Whitney U (非参, 秩和)
输出 p 值表 + 判定 (显著 < 0.05)。
"""
import csv
import math
import os
from collections import defaultdict
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "..", "..", "..", "结果")


def welch_t(x, y):
    nx, ny = len(x), len(y)
    mx, my = sum(x) / nx, sum(y) / ny
    vx = sum((a - mx) ** 2 for a in x) / (nx - 1)
    vy = sum((a - my) ** 2 for a in y) / (ny - 1)
    se = math.sqrt(vx / nx + vy / ny)
    if se == 0:
        return float("inf"), 1.0
    t = (mx - my) / se
    # 自由度 (Welch-Satterthwaite)
    df = (vx / nx + vy / ny) ** 2 / (
        (vx / nx) ** 2 / (nx - 1) + (vy / ny) ** 2 / (ny - 1))
    # 双侧 t 分布 p 值 (不完全 beta 函数近似)
    p = 2 * _t_cdf(-abs(t), df)
    return t, p


def _t_cdf(t, df):
    # 用正则化不完全 beta: P(T<=t) = 1 - 0.5*I_{df/(df+t^2)}(df/2, 1/2)
    if t >= 0:
        return 1 - 0.5 * _betainc(df / (df + t * t), df / 2, 0.5)
    return 0.5 * _betainc(df / (df + t * t), df / 2, 0.5)


def _betainc(x, a, b):
    """正则化不完全 beta 函数 (连续分式, Lentz 算法)."""
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    # 用对称性取较小分式
    if x > (a + 1) / (a + b + 2):
        return 1 - _betainc(1 - x, b, a)
    # 级数展开 (x 小的一侧)
    ln_beta = math.lgamma(a) + math.lgamma(b) - math.lgamma(a + b)
    term = 1.0
    s = term
    for k in range(1, 5000):
        term *= x * (a + b + k - 1) / (a + k)
        s += term
        if abs(term) < 1e-14:
            break
    return math.exp(a * math.log(x) + b * math.log1p(-x) - ln_beta) * s / a


def mann_whitney_u(x, y):
    """双侧 Mann-Whitney U (精确 p 值, 小样本; 大样本正态近似)."""
    nx, ny = len(x), len(y)
    pooled = sorted([(v, 0) for v in x] + [(v, 1) for v in y])
    ranks = {}
    i = 0
    while i < len(pooled):
        j = i
        while j + 1 < len(pooled) and pooled[j + 1][0] == pooled[i][0]:
            j += 1
        r = (i + j) / 2 + 1
        for k in range(i, j + 1):
            ranks[pooled[k]] = r
        i = j + 1
    u1 = sum(ranks[(v, 0)] for v in x) - nx * (nx + 1) / 2
    u = min(u1, nx * ny - u1)
    mu = nx * ny / 2
    sigma = math.sqrt(nx * ny * (nx + ny + 1) / 12)
    z = (u - mu) / sigma if sigma else 0.0
    # 正态近似双侧 p
    p = math.erfc(abs(z) / math.sqrt(2))
    return p


def main():
    rows = list(csv.DictReader(open(os.path.join(RES, "ablation_summary.tsv")),
                               delimiter="\t"))
    by = defaultdict(list)
    for r in rows:
        if r["group"] == "main" and r["cond"] != "n_align":
            by[r["cond"]].append(float(r["peak_epoch"]))
    base = by["baseline"]
    print(f"{'cond':<16}{'n':<4}{'peak':<12}{'t':<8}{'p_t':<10}{'p_mw':<10}")
    for cond in sorted(by):
        if cond == "baseline":
            continue
        x = by[cond]
        t, pt = welch_t(base, x)
        pmw = mann_whitney_u(base, x)
        m = sum(x) / len(x)
        print(f"{cond:<16}{len(x):<4}{m:>5.1f}±{_sd(x):<5.1f}"
              f"{t:>6.2f}  {pt:<10.4f}{pmw:<10.4f}")


def _sd(x):
    m = sum(x) / len(x)
    return math.sqrt(sum((a - m) ** 2 for a in x) / (len(x) - 1))


if __name__ == "__main__":
    main()
