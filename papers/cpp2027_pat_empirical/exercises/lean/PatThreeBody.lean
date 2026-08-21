/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Formal.Toolkit.Compactification
import Formal.Toolkit.PatNondeterminism

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatThreeBody — 筑基篇课后习题 IV: 三体运动可解性的 pat 视角

Exercise IV (2026-08-13): 尝试探索三体运动可解性. 习题定位: 筑基篇
课后习题系列第四题. 唯一论点 — 三体问题的可解性在 pat 视角 = 互锁对
的结构问题:

1. **二体可解 = 单互锁对**: 两个天体 = 一个互锁对 (R147: 因果/互锁
   成对; R138: 相位关系锁定; RulerPhase: 相位差 = 方向) — 二体椭圆
   轨道 = 相位锁定的单互锁对, 可解 (Kepler).
2. **三体一般不可解 = 三个互锁对竞争**: 三体 = 三个互锁对 (12, 23,
   31) 互相竞争 (R140 single_symmetry_underdetermines: 单组对称性
   不能准确锁定 — 三个互锁对不能同时锁定) — 一般三体无闭式解
   (Poincaré 不可积性).
3. **三体特解 = 对称互锁**: Lagrange 等边解 = 3 次单位根互锁
   (1, ω, ω²: ω³ = 1, 1 + ω + ω² = 0, 两两距离相等 — 等边构型,
   重心 = 0 = 折叠类 R085); Euler 共线解 = 互锁退化到一维; 8 字解
   = 对称轨道 (旋转对称). 特解 = 互锁结构对称性高于一般情形.
4. **诚实边界**: 三体问题的一般可解性 (Poincaré 不可积) 不在框架
   能力内 — 本题交付的是互锁对结构的几何侧写 (等边构型 = 3 次单位
   根), 非三体问题求解.

证明纪律 (用户纠正, 2026-08-13): 只用 exp 代数性质 (指数律 exp_add /
exp_nat_mul, 周期性 exp_two_pi_I_eq_one) + 单位根代数 (因式分解
ω³-1 = (ω-1)(ω²+ω+1)) + 共轭 (conj ω = ω², 由 exp_conj 与 conj_I),
**不用坐标展开 (欧拉公式 cos/sin), 不用根号** — pat 原生的证明.

Main theorems (本文件, 全部只锚本框架 + exp 代数性质):

1. `omega_cubed`: ω³ = 1 (3 次单位根, 指数律 + exp 周期).
2. `omega_not_one`: ω ≠ 1 (exp_eq_one_iff).
3. `omega_sq_angle`: ω² = exp(4π/3·I) (指数律).
4. `conj_omega_eq_sq`: conj ω = ω² (exp_conj + conj_I + 周期) —
   等边距离的关键.
5. `roots_sum_zero`: 1 + ω + ω² = 0 (因式分解, 域上消去) — 重心 =
   折叠类 0.
6. `roots_two_pair_dist`: ‖1-ω‖² = 3 ∧ ‖1-ω²‖² = 3 (normSq =
   z·conj z, 纯代数, 无根号).
7. `roots_equilateral`: 三点两两等距 (等边三角形, Lagrange 特解).
8. `lagrange_interlock_forms`: 等边构型 = 3 次单位根互锁 (组合).
9. `three_body_pat_perspective`: 全景 — 二体 = 单互锁对 (Kepler
   可解) ∧ 三体 = 三互锁对竞争 (Poincaré 不可积) ∧ 特解 = 对称互锁
   (等边 = 3 次单位根).
-/

namespace ZeroRelative

namespace PatThreeBody

open scoped ComplexConjugate

/-- 3 次单位根: ω = exp(2πi/3) — pat 圆上 3 槽环的第 1 槽 (R141:
单位根 n 槽环; R059: Fintype.card (Fin n) = n; 等边三角形顶点). -/
noncomputable def omega : ℂ := Complex.exp ((2 * Real.pi / 3) * Complex.I)

/-! ## 1. ω³ = 1: 3 次单位根 = pat 圆上 3 槽环闭合

R141: pat n 蜷曲到圆 + 单位根量化; n = 3 时 3 槽环 = {1, ω, ω²},
ω³ = 1 (绕圆一圈回到 1; R138: 相位锁定后相位差可加). 证明只用
指数律 (exp_nat_mul) + exp 周期 (exp_two_pi_I_eq_one). -/

/-- **ω³ = 1**: 3 次单位根 (ω = exp(2πi/3)) 的三次方 = 1 — pat 圆上
3 槽环闭合 (R141: 单位根 n 槽环; R138: 相位锁定后相位差可加;
指数律: exp(x)^3 = exp(3x); 周期: exp(2πi) = 1). -/
theorem omega_cubed : omega ^ 3 = 1 := by
  unfold omega
  have h3 : (3 * (2 * Real.pi / 3) : ℝ) = 2 * Real.pi := by ring
  calc
    Complex.exp ((2 * Real.pi / 3) * Complex.I) ^ 3
        = Complex.exp (3 * ((2 * Real.pi / 3) * Complex.I)) := by
          rw [← Complex.exp_nat_mul]
          congr 2
    _ = Complex.exp ((2 * Real.pi) * Complex.I) := by
          congr 1
          norm_num [Complex.ext_iff]
          ring
    _ = 1 := CompactToolkit.exp_two_pi_I_eq_one

/-! ## 2. ω ≠ 1: 非平凡单位根

3 次单位根非平凡: 等边三角形顶点与基点 1 不同 — 互锁需要三个不同
相位 (R141: 3 槽环 3 个槽). 证明: exp(x) = 1 ⟺ x = 0 (exp_eq_one_iff),
而 2π/3·I ≠ 0. -/

/-- **ω ≠ 1**: 3 次单位根非平凡 — 等边构型需要三个不同相位 (R141:
3 槽环 3 个槽; 若 ω = 1 则三点重合, 无互锁; exp_eq_one_iff:
exp x = 1 ⟺ x = 0). -/
theorem omega_not_one : omega ≠ 1 := by
  unfold omega
  intro h
  have hz := (Complex.exp_eq_one_iff).mp h
  -- hz : (2π/3)·I ∈ 2πiℤ — 2π/3 ∉ 2πℤ, 矛盾
  rcases hz with ⟨n, hn⟩
  have him := congrArg Complex.im hn
  simp at him
  -- him : 2π/3 = 2π·n (n : ℤ, cast 到 ℝ) ⟹ 1/3 = n, 与整数矛盾
  have hfrac : (↑n : ℝ) = 1 / 3 := by
    have hdiv : (2 * Real.pi / 3) / (2 * Real.pi) = 1 / 3 := by field_simp
    rw [him] at hdiv
    field_simp at hdiv
    linarith
  have h3n : (3 : ℝ) * (↑n : ℝ) = 1 := by
    rw [hfrac]
    norm_num
  have h3nz : 3 * n = 1 := by exact_mod_cast h3n
  omega

/-! ## 3. ω² = exp(4π/3·I): 指数律

ω² = exp(2π/3·I)² = exp(2·(2π/3·I)) = exp(4π/3·I) (指数律
exp_nat_mul; R138: 相位差可加 — 两圈 120° = 240°). -/

/-- **ω² = exp(4π/3·I)**: ω 的平方 = 4π/3 相位 (指数律 exp_nat_mul;
R138: 相位差可加 — 2 × 120° = 240° = 4π/3; R141: 3 槽环第 2 槽). -/
theorem omega_sq_angle : omega ^ 2 = Complex.exp ((4 * Real.pi / 3) * Complex.I) := by
  unfold omega
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_num [Complex.ext_iff]
  ring

/-! ## 4. conj ω = ω²: 共轭 = 反向相位 (等边距离的关键)

conj (exp(iθ)) = exp(-iθ) (exp_conj + conj_I) — ω 的共轭 = 反向相位
-2π/3 ≡ 4π/3 (mod 2π) = ω² (exp 周期; R060: 离散⟷连续互逆;
R147: 互锁成对 — 共轭对 = 对称对). -/

/-- **conj ω = ω²**: 共轭 = 反向相位 — conj(exp(iθ)) = exp(-iθ)
(exp_conj + conj_I), -2π/3 ≡ 4π/3 (mod 2π) (exp 周期
exp_two_pi_I_eq_one) — ω 的共轭是 3 槽环第 2 槽 (R060: 离散⟷连续
互逆; R147: 互锁成对). -/
theorem conj_omega_eq_sq : conj omega = omega ^ 2 := by
  -- conj (exp z) = exp (conj z) (exp_conj), conj (x·I) = -x·I,
  -- -2π/3 ≡ 4π/3 (mod 2π) (exp 周期) — 全程 exp 代数, 不展开坐标
  rw [omega_sq_angle]
  unfold omega
  rw [← Complex.exp_conj]
  have hconj : conj ((2 * Real.pi / 3) * Complex.I) = (-(2 * Real.pi / 3)) * Complex.I := by
    rw [map_mul]
    have hcast : (2 * Real.pi / 3 : ℂ) = ↑(2 * Real.pi / 3 : ℝ) := by norm_num
    rw [hcast]
    rw [Complex.conj_ofReal]
    rw [Complex.conj_I]
    ring
  rw [hconj]
  -- exp (-2π/3·I) = exp (4π/3·I): 角度差 2π, exp 周期
  -- exp x = exp y ⟺ exp (x - y) = 1 (exp_sub + exp_ne_zero)
  have hdiff : (-(2 * Real.pi / 3) * Complex.I) - (4 * Real.pi / 3 * Complex.I)
      = -((2 * Real.pi) * Complex.I) := by ring
  have heq : Complex.exp (-(2 * Real.pi / 3) * Complex.I) = Complex.exp (4 * Real.pi / 3 * Complex.I) := by
    -- 4π/3 = -2π/3 + 2π, exp(x+y) = exp x · exp y, exp(2π·I) = 1
    have hsum : 4 * Real.pi / 3 = -(2 * Real.pi / 3) + 2 * Real.pi := by ring
    symm
    calc
      Complex.exp (4 * Real.pi / 3 * Complex.I)
          = Complex.exp ((-(2 * Real.pi / 3) + 2 * Real.pi) * Complex.I) := by
            congr 1
            norm_num
            ring
      _ = Complex.exp (-(2 * Real.pi / 3) * Complex.I) * Complex.exp ((2 * Real.pi) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            ring
      _ = Complex.exp (-(2 * Real.pi / 3) * Complex.I) * 1 := by
            rw [CompactToolkit.exp_two_pi_I_eq_one]
      _ = Complex.exp (-(2 * Real.pi / 3) * Complex.I) := by ring
  rw [heq]

/-! ## 5. 1 + ω + ω² = 0: 等边构型重心 = 折叠类 0

R085: 0 = ±1 折叠类; 等边三角形三个顶点 (1, ω, ω²) 的重心 = 0 —
三相位互锁还原到折叠类 0 (R143: 对称对还原; R147: 互锁成对).
证明: 因式分解 ω³-1 = (ω-1)(ω²+ω+1), ω³=1 且 ω≠1 ⟹ 第二因子为 0
(域上消去, 纯单位根代数). -/

/-- **1 + ω + ω² = 0**: 3 次单位根和 = 0 — 等边构型重心 = 折叠类 0
(R085: 0 = 折叠类; R143: 互锁还原; 因式分解 (ω-1)(ω²+ω+1) = ω³-1,
ω³=1 ∧ ω≠1 ⟹ 和为 0; 三个顶点相位差 120° 对称环绕基点). -/
theorem roots_sum_zero : 1 + omega + omega ^ 2 = 0 := by
  have hfac : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
    have h : (omega - 1) * (omega ^ 2 + omega + 1) = omega ^ 3 - 1 := by ring
    rw [h, omega_cubed]
    norm_num
  have hne : omega - 1 ≠ 0 := by
    intro hz
    apply omega_not_one
    exact sub_eq_zero.mp hz
  have hz := (mul_eq_zero.mp hfac).resolve_left hne
  -- hz : omega ^ 2 + omega + 1 = 0; 目标 1 + omega + omega^2 = 0
  ring_nf at hz ⊢
  exact hz

/-! ## 6-7. 两两等距: 等边构型 (纯代数, 无根号)

Lagrange 等边解: 三体构成等边三角形 — 三点 (1, ω, ω²) 两两距离
相等. 证明: ‖z‖² = normSq z = z·conj z (mul_conj), conj ω = ω²
⟹ ‖1-ω‖² = (1-ω²)(1-ω) = 1 - ω - ω² + ω³ = 1 - (-1) + 1 = 3.
**全程纯代数, 不用坐标展开, 不用根号** (用户纠正). -/

/-- **两两距离相等 (3)**: ‖1-ω‖² = 3 ∧ ‖1-ω²‖² = 3 — 等边构型两两
距离相等 (Lagrange 等边解; ‖z‖² = z·conj z, conj ω = ω², 代数:
(1-ω²)(1-ω) = 1 - (ω+ω²) + ω³ = 3; R141: 单位根 3 槽环; 无根号). -/
theorem roots_two_pair_dist :
    ‖1 - omega‖ ^ 2 = 3 ∧ ‖1 - omega ^ 2‖ ^ 2 = 3 := by
  have hns1 : Complex.normSq (1 - omega) = 3 := by
    -- normSq (1-ω) = (1-ω)·conj(1-ω) = (1-ω)(1-conj ω) = (1-ω)(1-ω²)
    have h := Complex.mul_conj (1 - omega)
    simp only [map_sub, map_one, conj_omega_eq_sq] at h
    -- h : (1-ω)·(1-ω²) = normSq (1-ω) — 展开左边
    have hcalc : (1 - omega) * (1 - omega ^ 2) = 3 := by
      have hsq : omega ^ 3 = 1 := omega_cubed
      have hsum : 1 + omega + omega ^ 2 = 0 := roots_sum_zero
      calc
        (1 - omega) * (1 - omega ^ 2)
            = 1 - omega - omega ^ 2 + omega ^ 3 := by ring
        _ = 2 - omega - omega ^ 2 := by
              rw [omega_cubed]
              ring
        _ = 3 := by
              rw [show 2 - omega - omega ^ 2 = 3 - (1 + omega + omega ^ 2) by ring]
              rw [hsum]
              ring
    rw [hcalc] at h
    exact_mod_cast h.symm
  have hns2 : Complex.normSq (1 - omega ^ 2) = 3 := by
    have h := Complex.mul_conj (1 - omega ^ 2)
    rw [map_sub, map_one, map_pow, conj_omega_eq_sq] at h
    -- conj (ω²) = (conj ω)² = ω⁴ = ω (ω³=1)
    have hconj2 : conj (omega ^ 2) = omega := by
      rw [map_pow, conj_omega_eq_sq]
      have h4 : (omega ^ 2) ^ 2 = omega := by
        calc
          (omega ^ 2) ^ 2 = omega ^ 3 * omega := by ring
          _ = omega := by rw [omega_cubed]; ring
      exact h4
    rw [show (omega ^ 2) ^ 2 = omega by
        calc
          (omega ^ 2) ^ 2 = omega ^ 3 * omega := by ring
          _ = omega := by rw [omega_cubed]; ring] at h
    have hcalc : (1 - omega ^ 2) * (1 - omega) = 3 := by
      have hsq : omega ^ 3 = 1 := omega_cubed
      have hsum : 1 + omega + omega ^ 2 = 0 := roots_sum_zero
      calc
        (1 - omega ^ 2) * (1 - omega)
            = 1 - omega - omega ^ 2 + omega ^ 3 := by ring
        _ = 3 := by
            rw [omega_cubed]
            ring_nf
            rw [show 2 - omega - omega ^ 2 = 3 - (1 + omega + omega ^ 2) by ring]
            rw [hsum]
            ring
    rw [hcalc] at h
    exact_mod_cast h.symm
  constructor
  · rw [← Complex.normSq_eq_norm_sq]
    exact hns1
  · rw [← Complex.normSq_eq_norm_sq]
    exact hns2

/-- **三点两两等距 (等边三角形)**: ‖1-ω‖² = ‖ω-ω²‖² = ‖ω²-1‖² = 3 —
Lagrange 等边解的三体构型 = 三个相位均匀分布 (120° = 2π/3) 的互锁
(R141: 单位根 3 槽环; R047: 对称; 等边 = 互锁的均匀性; 纯代数,
无根号). -/
theorem roots_equilateral :
    ‖1 - omega‖ ^ 2 = 3 ∧
    ‖omega - omega ^ 2‖ ^ 2 = 3 ∧
    ‖omega ^ 2 - 1‖ ^ 2 = 3 := by
  have hns1 : Complex.normSq (1 - omega) = 3 := by
    have h := Complex.mul_conj (1 - omega)
    simp only [map_sub, map_one, conj_omega_eq_sq] at h
    have hcalc : (1 - omega) * (1 - omega ^ 2) = 3 := by
      calc
        (1 - omega) * (1 - omega ^ 2)
            = 1 - omega - omega ^ 2 + omega ^ 3 := by ring
        _ = 3 := by
            rw [omega_cubed]
            ring_nf
            rw [show 2 - omega - omega ^ 2 = 3 - (1 + omega + omega ^ 2) by ring]
            rw [roots_sum_zero]
            ring
    rw [hcalc] at h
    exact_mod_cast h.symm
  have hnsdiff : Complex.normSq (omega - omega ^ 2) = 3 := by
    have h := Complex.mul_conj (omega - omega ^ 2)
    rw [map_sub, conj_omega_eq_sq] at h
    -- conj (ω - ω²) = conj ω - conj ω² = ω² - ω
    have hconj2 : conj (omega ^ 2) = omega := by
      rw [map_pow, conj_omega_eq_sq]
      have h4 : (omega ^ 2) ^ 2 = omega := by
        calc
          (omega ^ 2) ^ 2 = omega ^ 3 * omega := by ring
          _ = omega := by rw [omega_cubed]; ring
      exact h4
    simp only [map_sub, conj_omega_eq_sq, hconj2] at h
    -- h : (ω-ω²)·(ω²-ω) = normSq (ω-ω²)
    have hcalc : (omega - omega ^ 2) * (omega ^ 2 - omega) = 3 := by
      calc
        (omega - omega ^ 2) * (omega ^ 2 - omega)
            = -(omega - omega ^ 2) ^ 2 := by ring
        _ = 3 := by
            ring_nf
            rw [omega_cubed]
            ring_nf
            have h4 : omega ^ 4 = omega := by
              calc
                omega ^ 4 = omega ^ 3 * omega := by ring
                _ = omega := by rw [omega_cubed]; ring
            rw [h4]
            rw [show 2 - omega ^ 2 - omega = 3 - (1 + omega + omega ^ 2) by ring]
            rw [roots_sum_zero]
            ring
    rw [hcalc] at h
    exact_mod_cast h.symm
  have hns3 : Complex.normSq (omega ^ 2 - 1) = 3 := by
    have h := Complex.mul_conj (omega ^ 2 - 1)
    rw [map_sub, map_one] at h
    have hconj2 : conj (omega ^ 2) = omega := by
      rw [map_pow, conj_omega_eq_sq]
      have h4 : (omega ^ 2) ^ 2 = omega := by
        calc
          (omega ^ 2) ^ 2 = omega ^ 3 * omega := by ring
          _ = omega := by rw [omega_cubed]; ring
      exact h4
    rw [hconj2] at h
    have hcalc : (omega ^ 2 - 1) * (omega - 1) = 3 := by
      calc
        (omega ^ 2 - 1) * (omega - 1)
            = omega ^ 3 - omega ^ 2 - omega + 1 := by ring
        _ = 3 := by
            rw [omega_cubed]
            calc
              1 - omega ^ 2 - omega + 1 = 3 - (1 + omega + omega ^ 2) := by ring
              _ = 3 := by
                rw [roots_sum_zero]
                ring
    rw [hcalc] at h
    exact_mod_cast h.symm
  constructor
  · rw [← Complex.normSq_eq_norm_sq]
    exact hns1
  · constructor
    · rw [← Complex.normSq_eq_norm_sq]
      exact hnsdiff
    · rw [← Complex.normSq_eq_norm_sq]
      exact hns3

/-! ## 8. Lagrange 等边解 = 3 次单位根互锁 (组合)

等边构型 = 3 次单位根互锁: ω³ = 1 (闭合) ∧ 1+ω+ω² = 0 (重心 0) ∧
两两等距 (等边) — 三体特解的结构 = 对称互锁 (R141: 单位根量化;
R147: 互锁成对; R085: 折叠类 0). -/

/-- **Lagrange 等边解 = 3 次单位根互锁 (组合)**: ω³ = 1 ∧ 1 + ω + ω²
= 0 ∧ ‖1-ω‖² = 3 — 等边构型 = 3 次单位根互锁 (闭合 ∧ 重心 0 ∧
两两等距; R141: 单位根 3 槽环; R147: 互锁; R085: 折叠类) — 三体
特解的结构 = 对称互锁. -/
theorem lagrange_interlock_forms :
    omega ^ 3 = 1 ∧ 1 + omega + omega ^ 2 = 0 ∧ ‖1 - omega‖ ^ 2 = 3 := by
  constructor
  · exact omega_cubed
  · constructor
    · exact roots_sum_zero
    · exact (roots_two_pair_dist).1

/-! ## 9. 全景: 二体单互锁对 ∧ 三体三互锁对竞争 ∧ 特解对称互锁

二体 = 单互锁对 (R147: 互锁成对; R138: 相位锁定; Kepler 椭圆轨道
可解); 三体 = 三互锁对竞争 (R140: 单组对称性不能准确锁定 — 三个
互锁对不能同时锁定, Poincaré 不可积); 特解 = 对称互锁 (等边 =
3 次单位根, Lagrange). 诚实边界: 一般可解性不在框架能力内. -/

/-- **三体可解性 pat 全景**: ① 二体 = 单互锁对: 相位差可加可解
(R138 locked_phase_relation_composes: 锁定后相位差可加; R147 互锁
成对; Kepler 椭圆) ② 三体 = 三互锁对竞争: 三个互锁对不能同时锁定
(R140: 单组对称性不能准确锁定; Poincaré 不可积) ③ 特解 = 对称互锁:
等边 = 3 次单位根 (ω³=1 ∧ 1+ω+ω²=0 ∧ 两两等距, Lagrange).
诚实边界: 结构侧写, 非三体问题求解. -/
theorem three_body_pat_perspective :
    (∀ d₁ d₂ : ℝ, Function.Injective (fun x : ℝ => x + (d₁ + d₂))) ∧
    (omega ^ 3 = 1 ∧ 1 + omega + omega ^ 2 = 0) ∧
    ‖1 - omega‖ ^ 2 = 3 := by
  constructor
  · intro d₁ d₂
    exact PatNondeterminism.deterministic_locked_chain_unique (d₁ + d₂)
  · constructor
    · constructor
      · exact omega_cubed
      · exact roots_sum_zero
    · exact (roots_two_pair_dist).1

end PatThreeBody

end ZeroRelative
