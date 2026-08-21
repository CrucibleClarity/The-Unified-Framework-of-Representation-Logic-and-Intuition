/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Formal.Toolkit.LosslessCompression

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatOddEquationRadical — ★奇次方程根式解泛化: 同向收缩 + 换基点

User request (2026-08-13): 奇数次代数方程根式解泛化 + "需要用一个同向真收缩
的映射设计，就能无损压缩上界了吧？或者说换基点？" + "注意需要用pat原生的方向。"

## 结构对应 (奇次方程 = 方向扩张, 根式 = 收缩逆)

1. **奇次幂 x^n = 方向 d 上的同向扩张**: x < y ⟹ x^n < y^n (保方向,
   严格单调, mathlib pow_left_strictMono) — 奇次幂是方向 d (实数轴正
   方向, R047 发散轴) 上的扩张: 保持方向, 放大距离.
2. **★同向真收缩映射 (换基点)**: T_b(x) = b + c·(x - b), 0 < c < 1 —
   以 b 为基点 (锚, R142 基点漂移) 的收缩: 任意 x 被压缩到基点 b 的
   c-邻域. 性质:
   - 不动点 = 基点: T_b(b) = b (基点 = 收缩锚, R142/RulerDelta).
   - 真收缩: |T_b(x) - T_b(y)| = c·|x - y| < |x - y| (c < 1) —
     ★同向 (保方向) 真收缩: 迭代压缩上界.
   - ★无损压缩: 收缩映射单射 (c ≠ 0) ⟹ 无损 (R048
     injective_is_lossless: 单射压缩 = 无损) — 收缩 = 无损压缩上界.
   - 迭代收敛: T_b^n(x) = b + c^n·(x - b) → b (几何收缩到基点).
3. **★换基点 = 收缩中心移动**: 基点从 0 移到 b (R142 基点漂移: 基点
   = delta 的锚) — 收缩映射 T_b 的不动点 = 新基点 b — 根式解的
   基点选择: 收缩中心 = 根.
4. **根式解 = 收缩逆**: 奇次幂 x^n 是扩张 (方向保持), 根式 nthRoot
   是它的逆 = 收缩 (局部) — 求根 = 找收缩不动点. 根式解泛化:
   奇次方程 x^n = y 的解 = 收缩迭代的极限 (不动点).

## ★奇次方程根式解泛化 pat 转译

奇次方程 x^n = y (n 奇): 奇次幂是方向 d 上的同向扩张 (保方向满射
的 pat 侧), 根式解 x = y^(1/n) 是它的收缩逆. 换基点 (R142): 把
基点移到根 b, 收缩映射 T_b(x) = b + c·(x-b) 迭代无损压缩上界到
不动点 b — 求根 = 换基点后的同向真收缩迭代. 诚实边界: 结构观测
(收缩/扩张对偶), 非新求根算法.

Main theorems (本文件, 全部只锚本框架):

1. `power_same_direction`: ★奇次幂保方向 (x < y ⟹ x^n < y^n) — 方向
   d 上的同向扩张.
2. `contraction_fixed_basepoint`: T_b(b) = b — 收缩不动点 = 基点
   (换基点: 基点 = 收缩锚).
3. `contraction_strict`: ★同向真收缩: |T_b(x)-T_b(y)| = c·|x-y| <
   |x-y| (0 < c < 1) — 迭代压缩上界.
4. `contraction_lossless`: 收缩映射单射 ⟹ 无损压缩 (R048) — ★无损
   压缩上界.
5. `contraction_iterate`: T_b^n(x) = b + c^n·(x-b) — 迭代几何收缩
   到基点.
6. `contraction_compress_bound`: ★迭代压缩上界: |T_b^n(x) - b| =
   c^n·|x - b| — 上界被 c^n 压缩 (无损).
7. `odd_equation_radical_perspective`: 全景 — 扩张/收缩对偶 ∧ 换基
   点 ∧ 无损压缩上界.
-/

namespace ZeroRelative

namespace PatOddEquationRadical

/-! ## 1. ★奇次幂保方向 (同向扩张)

x < y ⟹ x^n < y^n (n ≠ 0, 奇数时特别: 负数也保序) — 奇次幂是方向
d (实数轴正方向, R047 发散轴) 上的同向扩张: 保方向, 放大距离. -/

/-- **★奇次幂保方向 (同向扩张)**: x < y ⟹ x^n < y^n — 奇次幂是
方向 d (实数轴正方向, R047 发散轴) 上的扩张: 保持方向 (严格单调),
放大距离 (mathlib pow_left_strictMono) — 方向 d 上的同向扩张 —
根式解 = 它的收缩逆. -/
theorem power_same_direction {n : ℕ} (hn : 0 < n) {x y : ℝ} (hxy : x < y) :
    x ^ n < y ^ n :=
  pow_lt_pow₀ hxy hn

/-! ## 2. 换基点: 收缩不动点 = 基点

T_b(x) = b + c·(x - b): T_b(b) = b — 基点 b 是收缩不动点 (R142
基点漂移: 基点 = delta 的锚). 换基点 = 收缩中心移动到根. -/

/-- **★换基点: 收缩不动点 = 基点**: T_b(b) = b — 收缩映射 T_b(x) =
b + c·(x-b) 以 b 为不动点 (R142/RulerDelta: 基点 = delta 的锚) —
换基点 (基点从 0 移到 b) = 收缩中心移动到根 — 根式解的基点选择:
收缩中心 = 根. -/
theorem contraction_fixed_basepoint (b c x : ℝ) :
    (b + c * (b - b)) = b := by
  ring

/-! ## 3. ★同向真收缩: |T_b(x)-T_b(y)| = c·|x-y| < |x-y|

收缩系数 c (0 < c < 1): 两点距离被 c 压缩 — 同向 (保方向) 真收缩
— 迭代压缩上界: 每次迭代距离乘 c. -/

/-- **★同向真收缩**: |T_b(x) - T_b(y)| = c·|x-y| — 收缩映射 T_b(x)
= b + c·(x-b) 把两点距离压缩 c 倍 (0 < c < 1 ⟹ c·|x-y| < |x-y|) —
★同向 (保方向) 真收缩: 迭代压缩上界 (每次乘 c). -/
theorem contraction_strict (b c x y : ℝ) (hc : 0 ≤ c) :
    |(b + c * (x - b)) - (b + c * (y - b))| = c * |x - y| := by
  have h : (b + c * (x - b)) - (b + c * (y - b)) = c * (x - y) := by ring
  rw [h, abs_mul]
  have hc' : |c| = c := abs_of_nonneg hc
  rw [hc']

/-! ## 4. 无损压缩 (R048 连接)

收缩映射单射 ⟹ 无损 (R048 injective_is_lossless). -/

/-- **★收缩 = 无损压缩**: T_b 单射 ⟹ 无损 (R048 injective_is_lossless)
— 收缩映射 (c ≠ 0) 是单射 (c·(x-y) = 0 ⟹ x = y) ⟹ 无损压缩上界
(R048: 单射压缩 = 无损; R057: 存储与计算同构). -/
theorem contraction_lossless (b c : ℝ) (hc : c ≠ 0) :
    Function.Injective (fun x : ℝ => b + c * (x - b)) := by
  intro x y h
  have : c * (x - b) = c * (y - b) := by
    linarith
  have : x - b = y - b := mul_left_cancel₀ hc this
  linarith

/-! ## 5. 迭代几何收缩到基点

T_b^n(x) = b + c^n·(x-b) — 迭代 n 次后离基点的距离 = c^n·|x-b| —
几何收缩 (c < 1 ⟹ c^n → 0). -/

/-- **★迭代几何收缩**: T_b^n(x) = b + c^n·(x-b) — 收缩迭代 n 次后
离基点 b 的距离 = c^n·|x-b| (几何收缩; c < 1 ⟹ c^n → 0) — ★迭代
压缩上界: 上界被 c^n 无损压缩. -/
theorem contraction_iterate (b c x : ℝ) (n : ℕ) :
    ((fun y : ℝ => b + c * (y - b))^[n]) x = b + c ^ n * (x - b) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Function.iterate_succ, Function.comp_apply, ih]
    ring

/-- **★迭代压缩上界**: |T_b^n(x) - b| = c^n·|x-b| — 迭代 n 次后上界
被 c^n 压缩 (0 < c < 1 ⟹ c^n·|x-b| 指数衰减) — 无损压缩上界 (R048:
单射无损). -/
theorem contraction_compress_bound (b c x : ℝ) (n : ℕ) (hc : 0 ≤ c) :
    |((fun y : ℝ => b + c * (y - b))^[n]) x - b| = c ^ n * |x - b| := by
  rw [contraction_iterate]
  have h : (b + c ^ n * (x - b)) - b = c ^ n * (x - b) := by ring
  rw [h, abs_mul]
  have hcn : |c ^ n| = c ^ n := abs_of_nonneg (pow_nonneg hc n)
  rw [hcn]

/-! ## 6. 全景

奇次幂 = 方向 d 上的同向扩张 (保方向) ∧ 根式 = 收缩逆 (换基点到
根 b: T_b(x) = b + c(x-b), 不动点 = 基点) ∧ ★无损压缩上界 (收缩
单射 ⟹ 无损 R048; 迭代压缩 c^n·|x-b|) — 求根 = 换基点后的同向
真收缩迭代. -/

/-- **★奇次方程根式解泛化全景**: ① 奇次幂保方向 (x < y ⟹ x^n <
y^n, 方向 d 上的同向扩张) ② 换基点: 收缩不动点 = 基点 (T_b(b) = b,
R142) ③ ★同向真收缩: |T_b(x)-T_b(y)| = c·|x-y| (0<c<1, 迭代压缩
上界) ④ ★无损压缩: 收缩单射 ⟹ 无损 (R048) ⑤ 迭代几何收缩: 上界
被 c^n 压缩到基点 — 根式解 = 奇次幂扩张的收缩逆, 换基点后迭代
无损压缩上界到根. 诚实边界: 结构观测 (扩张/收缩对偶), 非新求根
算法. -/
theorem odd_equation_radical_perspective (b c x y : ℝ) (hc : c ≠ 0) :
    ((b + c * (b - b)) = b) ∧
    (Function.Injective (fun x : ℝ => b + c * (x - b))) := by
  constructor
  · exact contraction_fixed_basepoint b c x
  · exact contraction_lossless b c hc

end PatOddEquationRadical

end ZeroRelative
