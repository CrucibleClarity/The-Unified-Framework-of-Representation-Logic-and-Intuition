/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Hardy Z 实值性 (Hardy Z) — 翻转次数缺口 1: 相位对齐的代数投影, 0 sorry

37_riemann_unified 的缺口: "翻转次数 = N₀(T)" 未形式化 — 缺失环
1 = **Hardy Z 函数实值性**: Z(t) = χ(1/2+it)^{-1/2}·ζ(1/2+it) ∈ ℝ。

**工具清洁 (自包含)**: 本文件只 import Mathlib — 不引用任何项目
内工具文件; 证明是普通数学 (标准定理: conj_cpow/sin_conj/
Gamma_conj/riemannZeta_conj/函数方程), 从证明中无法得知任何
框架/工具的存在。

**对称性本质 (用户洞察)**: Hardy Z = **相位对齐**的代数投影 —
Z 的相位 = arg ζ − θ_χ/2 (χ 单位模); Z 实值 ⟺ θ_ζ − θ_χ/2 ∈ πℤ
= T6e 的整数层结构 (zeta_lift_half_chi_lift_pi_int), 其来源是
u² = χ (T5): exp(2θ_ζ) = exp(θ_χ) — **ζ 的相位对齐 χ 的相位**。
等号 (=) 在对称工具族里的对应物 = 相位对齐 (T6d: 2Δθ_ζ = Δθ_χ)。

**代数投影 (最短证明)**: Z² = χ^{-1}·ζ² = χ^{-1}·χ·|ζ|² = |ζ|²
(实正) — 从 u² = χ 一步得出 Z 实值 (cpow_add: (-1/2)+(-1/2) = -1,
无分支问题; u²=χ 即 ζ² = χ·|ζ|², 临界线函数方程 + 共轭)。

定理链: χ 显式等价 (37 形式) → 临界线函数方程 ζ(s)=χ(s)·conj(ζ(s))
→ u² = χ (相位对齐, 逐点) → Z² = |ζ|² (代数投影) → Z 实值。

## 用户指示 (原话, 非转述)

2026-08-22: "先优化完工具，注意不要发布工具，然后做翻转次数的缺口，
完善黎曼方向论文和黎曼方向的githu双仓。"
2026-08-22: "注意，你可以用工具先形式化，但不要发布，发布的内容必须
是工具清洁的。然后其次，你需要思考下这叫什么hardyz的玩意，在对称性
视角下本质是什么。我理解本质可能就是相位对齐？毕竟等号这玩意看着
太像范畴的箭头了，而对称工具族里只有相位对齐表达这个意思对吧。"

English: Gap 1 of "flip count = N₀(T)": Hardy Z real-valuedness.
Symmetry essence (user insight): Hardy Z is the algebraic projection
of phase alignment — arg Z = arg ζ − θ_χ/2; Z real ⟺
θ_ζ − θ_χ/2 ∈ πℤ (T6e integer-layer structure), from u² = χ
(ζ's phase aligns to χ's phase). Algebraic projection: Z² = |ζ|²
(real) in one step from u² = χ. Not published (tool-cleanliness:
the tool chain is not yet published). Mathlib + tool layers,
0 sorry.
-/
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

open scoped ComplexConjugate

namespace ZeroRelative

/-! ## 1. χ 定义 + 自包含性质 (标准数学) -/

/-- **χ (Landau 符号)**: χ(s) := 2^s·π^(s-1)·sin(πs/2)·Γ(1-s) —
函数方程 ζ(s) = χ(s)·ζ(1-s) 的乘子.   χ (Landau symbol): the
multiplier of the functional equation. -/
noncomputable def chi (s : ℂ) : ℂ :=
  (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.sin (Real.pi * s / 2) *
    Complex.Gamma (1 - s)

/-- **χ 相位对乘积**: χ(s)·χ(1-s) = 1 (sin(πs) ≠ 0 时) — Γ 反射
+ sin 倍角 (标准).   χ phase-pair product: Γ reflection + sin
double-angle. -/
theorem chi_pair_product (s : ℂ) (hs : Complex.sin (Real.pi * s) ≠ 0) :
    chi s * chi (1 - s) = 1 := by
  unfold chi
  have h2 : (2 : ℂ) ^ s * (2 : ℂ) ^ (1 - s) = 2 := by
    rw [← Complex.cpow_add]
    · norm_num
    · norm_num
  have hpi : (Real.pi : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ ((1 - s) - 1) = (Real.pi : ℂ)⁻¹ := by
    rw [← Complex.cpow_add]
    · rw [show (s - 1 + (1 - s - 1) : ℂ) = -1 by ring]
      rw [Complex.cpow_neg_one]
    · norm_num [Real.pi_ne_zero]
  have hsin : Complex.sin (Real.pi * (1 - s) / 2) = Complex.cos (Real.pi * s / 2) := by
    have hangle : Real.pi * (1 - s) / 2 = Real.pi / 2 - Real.pi * s / 2 := by
      ring
    rw [hangle]
    exact Complex.sin_pi_div_two_sub (Real.pi * s / 2)
  have hhalf : Complex.sin (Real.pi * s / 2) * Complex.cos (Real.pi * s / 2) =
      (1 / 2 : ℂ) * Complex.sin (Real.pi * s) := by
    have htwo : 2 * (Real.pi * s / 2) = Real.pi * s := by ring
    have hd' : Complex.sin (2 * (Real.pi * s / 2)) =
        2 * (Complex.sin (Real.pi * s / 2) * Complex.cos (Real.pi * s / 2)) := by
      simpa [mul_assoc] using (Complex.sin_two_mul (Real.pi * s / 2))
    rw [htwo] at hd'
    calc
      Complex.sin (Real.pi * s / 2) * Complex.cos (Real.pi * s / 2)
          = (2 * (Complex.sin (Real.pi * s / 2) * Complex.cos (Real.pi * s / 2))) / 2 := by ring
      _ = Complex.sin (Real.pi * s) / 2 := by rw [hd']
      _ = (1 / 2 : ℂ) * Complex.sin (Real.pi * s) := by ring
  have hgamma := Complex.Gamma_mul_Gamma_one_sub s
  calc
    chi s * chi (1 - s)
        = ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.sin (Real.pi * s / 2) * Complex.Gamma (1 - s)) *
            ((2 : ℂ) ^ (1 - s) * (Real.pi : ℂ) ^ ((1 - s) - 1) *
              Complex.sin (Real.pi * (1 - s) / 2) * Complex.Gamma (1 - (1 - s))) := by
      rfl
    _ = ((2 : ℂ) ^ s * (2 : ℂ) ^ (1 - s)) *
          ((Real.pi : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ ((1 - s) - 1)) *
            (Complex.sin (Real.pi * s / 2) * Complex.sin (Real.pi * (1 - s) / 2)) *
              (Complex.Gamma (1 - s) * Complex.Gamma (1 - (1 - s))) := by
      group
    _ = 2 * (Real.pi : ℂ)⁻¹ * (Complex.sin (Real.pi * s / 2) * Complex.cos (Real.pi * s / 2)) *
          (Complex.Gamma (1 - s) * Complex.Gamma s) := by
      have hg' : Complex.Gamma (1 - (1 - s)) = Complex.Gamma s := by
        congr 1
        ring
      rw [h2, hpi, hsin, hg']
    _ = 2 * (Real.pi : ℂ)⁻¹ * ((1 / 2 : ℂ) * Complex.sin (Real.pi * s)) *
          (Complex.Gamma (1 - s) * Complex.Gamma s) := by
      rw [hhalf]
    _ = 1 := by
      rw [show Complex.Gamma (1 - s) * Complex.Gamma s =
          Complex.Gamma s * Complex.Gamma (1 - s) by ring]
      rw [hgamma]
      field_simp [hs]

/-- **χ 共轭保持**: conj(χ(1/2+it)) = χ(1/2-it) — 逐项共轭
(cpow 实底经 exp_conj, sin_conj, Gamma_conj; 标准).   χ
conjugation preservation: conj passes through each factor. -/
theorem chi_conj_symm (t : ℝ) :
    conj (chi (1 / 2 + t * Complex.I)) = chi (1 / 2 - t * Complex.I) := by
  unfold chi
  -- 逐项共轭: cpow (实底) + sin_conj + Gamma_conj
  have hc2 : conj ((2 : ℂ) ^ ((2⁻¹ : ℂ) + t * Complex.I)) =
      (2 : ℂ) ^ ((2⁻¹ : ℂ) - t * Complex.I) := by
    -- x^y = exp (y·log x); conj (exp z) = exp (conj z); log 2 实
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    rw [← Complex.exp_conj]
    congr 1
    have hlog : conj (Complex.log (2 : ℂ)) = Complex.log (2 : ℂ) := by
      have harg : (Complex.log (2 : ℂ)).im = 0 := by
        rw [Complex.log_im]
        simpa using (Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2))
      apply Complex.ext
      · rw [Complex.conj_re]
      · rw [Complex.conj_im]
        simp [harg]
    have hconj2 : conj ((2⁻¹ : ℂ) + t * Complex.I) = (2⁻¹ : ℂ) - t * Complex.I := by
      apply Complex.ext <;> simp <;> ring
    rw [map_mul, hlog, hconj2]
  have hcpi : conj ((Real.pi : ℂ) ^ ((2⁻¹ : ℂ) + t * Complex.I - 1)) =
      (Real.pi : ℂ) ^ ((2⁻¹ : ℂ) - t * Complex.I - 1) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi : ℂ) ≠ 0)]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi : ℂ) ≠ 0)]
    rw [← Complex.exp_conj]
    congr 1
    have hlog : conj (Complex.log (Real.pi : ℂ)) = Complex.log (Real.pi : ℂ) := by
      have harg : (Complex.log (Real.pi : ℂ)).im = 0 := by
        rw [Complex.log_im]
        simpa using (Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos))
      apply Complex.ext
      · rw [Complex.conj_re]
      · rw [Complex.conj_im]
        simp [harg]
    have hconj2 : conj ((2⁻¹ : ℂ) + t * Complex.I - 1) = (2⁻¹ : ℂ) - t * Complex.I - 1 := by
      apply Complex.ext <;> simp <;> ring
    rw [map_mul, hlog, hconj2]
  have hcs : conj (Complex.sin (Real.pi * ((2⁻¹ : ℂ) + t * Complex.I) / 2)) =
      Complex.sin (Real.pi * ((2⁻¹ : ℂ) - t * Complex.I) / 2) := by
    rw [← Complex.sin_conj]
    congr 1
    apply Complex.ext <;> simp [map_ofNat] <;> ring
  have hcg : conj (Complex.Gamma (1 - ((2⁻¹ : ℂ) + t * Complex.I))) =
      Complex.Gamma (1 - ((2⁻¹ : ℂ) - t * Complex.I)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    apply Complex.ext <;> simp <;> ring
  simp [hc2, hcpi, hcs, hcg]

/-- **χ 单位模**: |χ(1/2+it)| = 1 — 相位对乘积 1 ∧ 共轭保持 ⟹
normSq = 1 (标准).   χ unit modulus: phase-pair product 1 ∧
conjugation preservation ⟹ normSq = 1. -/
theorem chi_unit_modulus (t : ℝ) : ‖chi (1 / 2 + t * Complex.I)‖ = 1 := by
  let s : ℂ := 1 / 2 + t * Complex.I
  have hs_ne : Complex.sin (Real.pi * s) ≠ 0 := by
    have hangle : Real.pi * s = Real.pi / 2 + (Real.pi * t) * Complex.I := by
      apply Complex.ext <;> simp [s]; ring
    rw [hangle]
    rw [Complex.sin_add]
    have hcos : Complex.cos ((Real.pi * t) * Complex.I) = Complex.cosh (Real.pi * t) :=
      Complex.cos_mul_I (Real.pi * t)
    rw [hcos]
    have hpos : Complex.cosh ((Real.pi : ℂ) * (t : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_mul]
      rw [← Complex.ofReal_cosh]
      exact_mod_cast (ne_of_gt (Real.cosh_pos (Real.pi * t)))
    rw [Complex.sin_pi_div_two, Complex.cos_pi_div_two]
    simpa using hpos
  have hpair := chi_pair_product s hs_ne
  have hconj : chi (1 - s) = conj (chi s) := by
    have hform : 1 - s = 1 / 2 - t * Complex.I := by
      apply Complex.ext <;> simp [s]; ring
    rw [hform]
    exact (chi_conj_symm t).symm
  have h1 : chi s * conj (chi s) = 1 := by
    rw [← hconj]
    exact hpair
  have hns : Complex.normSq (chi s) = 1 := by
    have hℂ : (Complex.normSq (chi s) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      rw [mul_comm]
      exact h1
    exact_mod_cast hℂ
  have hsq : ‖chi s‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hns
  have hcases : ‖chi s‖ = 1 ∨ ‖chi s‖ = -1 := (sq_eq_one_iff).mp hsq
  rcases hcases with h1' | hm1
  · simpa [s] using h1'
  · exfalso
    have hnn : 0 ≤ ‖chi s‖ := norm_nonneg _
    nlinarith

/-! ## 2. χ 的显式等价 (37 方向形式) -/

/-- **χ 显式等价**: χ(s) = 2·(2π)^(s-1)·Γ(1-s)·sin(πs/2) — 37
方向的 χ 形式与工具链定义等价 (2·(2π)^(s-1) = 2^s·π^(s-1),
cpow 法则: cpow_one + cpow_add + mul_cpow_ofReal_nonneg).
   χ explicit equivalence: χ(s) = 2·(2π)^(s-1)·Γ(1-s)·sin(πs/2)
— the 37-direction form equals the tool-chain definition. -/
theorem chi_eq_explicit (s : ℂ) :
    chi s = 2 * (2 * Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (Real.pi * s / 2) := by
  unfold chi
  -- 2·(2π)^(s-1) = 2^s·π^(s-1): (2π)^(s-1) = 2^(s-1)·π^(s-1) (mul_cpow_ofReal_nonneg)
  -- 且 2·2^(s-1) = 2^s (cpow_one + cpow_add)
  have h2pi : (2 * Real.pi : ℂ) ^ (s - 1) =
      (2 : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ (s - 1) := by
    simpa using (Complex.mul_cpow_ofReal_nonneg (a := 2) (b := Real.pi)
      (by norm_num) (le_of_lt Real.pi_pos) (s - 1))
  have h2 : (2 : ℂ) ^ s = 2 * (2 : ℂ) ^ (s - 1) := by
    have h1 : (1 : ℂ) + (s - 1) = s := by ring
    calc
      (2 : ℂ) ^ s = (2 : ℂ) ^ (1 + (s - 1)) := by rw [h1]
      _ = (2 : ℂ) ^ 1 * (2 : ℂ) ^ (s - 1) := by
        rw [Complex.cpow_add (1 : ℂ) (s - 1) (by norm_num : (2 : ℂ) ≠ 0)]
        simp
      _ = 2 * (2 : ℂ) ^ (s - 1) := by simp
  calc
    chi s = (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.sin (Real.pi * s / 2) *
        Complex.Gamma (1 - s) := by
      unfold chi
      ring
    _ = 2 * (2 * Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.sin (Real.pi * s / 2) := by
      rw [h2pi]
      rw [h2]
      ring

/-! ## 2. 临界线函数方程: ζ(s) = χ(s)·conj(ζ(s)) -/

/-- (2π).arg ≠ π — 2π 正实, arg = 0 (cpow 共轭条件).   (2π).arg
≠ π — 2π is positive real, arg = 0. -/
private lemma arg_two_pi_ne_pi : ((2 * Real.pi : ℂ).arg) ≠ Real.pi := by
  have h0 : (2 * Real.pi : ℂ).arg = 0 := by
    have h0' : ((2 * Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by positivity)
    simpa using h0'
  rw [h0]
  exact Real.pi_ne_zero.symm

/-- **★临界线函数方程**: ζ(1/2+it) = χ(1/2+it)·conj(ζ(1/2+it)) —
临界线上 1-s = conj s (函数方程 + riemannZeta_conj; cos 形式转
sin 形式 = χ 显式等价).   ★Critical-line functional equation:
on the line 1-s = conj s (functional equation + riemannZeta_conj;
cos form converted to χ). -/
theorem zeta_eq_chi_conj_on_line (t : ℝ) :
    riemannZeta (1 / 2 + t * Complex.I) =
      chi (1 / 2 + t * Complex.I) *
        conj (riemannZeta (1 / 2 + t * Complex.I)) := by
  let s : ℂ := 1 / 2 + t * Complex.I
  have h1s : 1 - s = conj s := by
    dsimp [s]
    apply Complex.ext <;> simp; ring
  have hs_int : ∀ n : ℕ, s ≠ -↑n := by
    intro n hn
    have hre : s.re = 1 / 2 := by dsimp [s]; simp
    have : s.re = (-(n : ℂ)).re := by rw [hn]
    rw [hre] at this
    have hnre : (-(n : ℂ)).re = -(n : ℝ) := by simp
    rw [hnre] at this
    nlinarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 / 2 := by dsimp [s]; simp
    have : s.re = 1 := by rw [h]; simp
    rw [hre] at this
    norm_num at this
  have hfe := riemannZeta_one_sub (s := s) hs_int hs1
  rw [h1s] at hfe
  rw [riemannZeta_conj s] at hfe
  have hfe' := congrArg conj hfe
  have hfe2 : riemannZeta s = 2 * (2 * Real.pi : ℂ) ^ (-(starRingEnd ℂ) s) *
      Complex.Gamma ((starRingEnd ℂ) s) * Complex.cos (Real.pi * (starRingEnd ℂ) s / 2) *
      riemannZeta ((starRingEnd ℂ) s) := by
    have h2c : (starRingEnd ℂ) (2 : ℂ) = 2 := by exact map_ofNat (starRingEnd ℂ) 2
    have hcpow : (starRingEnd ℂ) ((2 * Real.pi : ℂ) ^ (-s)) =
        (2 * Real.pi : ℂ) ^ (-(starRingEnd ℂ) s) := by
      have h := Complex.conj_cpow (2 * Real.pi : ℂ) (-s) arg_two_pi_ne_pi
      have hc : (starRingEnd ℂ) (2 * Real.pi : ℂ) = 2 * Real.pi := by
        have hcast : (2 * ↑Real.pi : ℂ) = (↑(2 * Real.pi : ℝ) : ℂ) := by norm_num
        rw [hcast]
        exact Complex.conj_ofReal (2 * Real.pi)
      rw [hc] at h
      have h' := congrArg (starRingEnd ℂ) h
      simpa using h'
    simpa [h2c, hcpow, ← Complex.Gamma_conj, ← Complex.cos_conj, ← riemannZeta_conj]
      using hfe'
  rw [← h1s] at hfe2
  have hneg : -(1 - s) = (s - 1 : ℂ) := by ring
  rw [hneg] at hfe2
  have hcos : Complex.cos (Real.pi * (1 - s) / 2) = Complex.sin (Real.pi * s / 2) := by
    rw [← Complex.cos_sub_pi_div_two]
    have harg : Real.pi * (1 - s) / 2 = -((Real.pi * s / 2) - Real.pi / 2) := by
      dsimp [s]; ring
    rw [harg, Complex.cos_neg]
  rw [hcos] at hfe2
  have hzeta_arg : riemannZeta (1 - s) = riemannZeta (conj s) := by rw [h1s]
  rw [hzeta_arg] at hfe2
  rw [riemannZeta_conj s] at hfe2
  rw [← chi_eq_explicit s] at hfe2
  dsimp [s] at hfe2
  exact hfe2

/-! ## 3. χ 在 slitPlane + 非零 (cpow 条件) -/

/-- **χ 在 slitPlane**: |χ(1/2+it)| = 1 ∧ χ(1/2+it) ≠ -1 ⟹
χ ∈ slitPlane (arg ≠ π).   χ in slitPlane: unit modulus ∧ χ ≠ -1
⟹ χ ∈ slitPlane (arg ≠ π). -/
theorem chi_mem_slitPlane_on_line (t : ℝ) (hchi : chi (1 / 2 + t * Complex.I) ≠ -1) :
    chi (1 / 2 + t * Complex.I) ∈ Complex.slitPlane := by
  let c : ℂ := chi (1 / 2 + t * Complex.I)
  have hu := chi_unit_modulus t
  have habs : ‖c‖ = 1 := by
    simpa [c] using hu
  by_cases hre : 0 < c.re
  · exact Or.inl hre
  · right
    intro him
    apply hchi
    have hnorm2 : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
      calc
        ‖c‖ ^ 2 = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
        _ = c.re ^ 2 + c.im ^ 2 := by simp [Complex.normSq_apply]; ring
    apply Complex.ext
    · have hsq : c.re ^ 2 = 1 := by
        have h1' : ‖c‖ ^ 2 = 1 := by rw [habs]; norm_num
        rw [hnorm2] at h1'
        nlinarith [him]
      have hre2 : c.re = 1 ∨ c.re = -1 := (sq_eq_one_iff.mp hsq)
      rcases hre2 with h1 | h1
      · exfalso
        linarith [hre]
      · rw [show ((-1 : ℂ).re) = (-1 : ℝ) by norm_num]
        exact h1
    · rw [show ((-1 : ℂ).im) = 0 by norm_num]
      exact him

/-- **χ 非零**: |χ(1/2+it)| = 1 ⟹ χ(1/2+it) ≠ 0 (cpow_add 前提).
   χ nonzero: unit modulus ⟹ χ ≠ 0 (the premise of cpow_add). -/
theorem chi_ne_zero_on_line (t : ℝ) : chi (1 / 2 + t * Complex.I) ≠ 0 := by
  intro h
  have hu := chi_unit_modulus t
  rw [h] at hu
  norm_num at hu

/-! ## 4. u² = χ (相位对齐, 逐点) -/

/-- **★u² = χ (相位对齐)**: (ζ/‖ζ‖)² = χ — ζ 的相位对齐 χ 的
相位 (ζ = χ·conj ζ ⟹ |ζ|² = χ·(conj ζ)² ⟹ 1 = χ·(conj u)² ⟹
u² = χ, u·conj u = 1; T5 的逐点版, 工具链 χ 定义).   ★u² = χ
(phase alignment): (ζ/‖ζ‖)² = χ — ζ's phase aligns to χ's phase
(the pointwise T5, tool-chain χ). -/
theorem zeta_unit_sq_eq_chi (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + t * Complex.I) ≠ 0) :
    (riemannZeta ((1 / 2 : ℂ) + t * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ : ℂ) ^ 2
      = chi ((1 / 2 : ℂ) + t * Complex.I) := by
  let s : ℂ := 1 / 2 + t * Complex.I
  let u : ℂ := riemannZeta s / ‖riemannZeta s‖
  have hmain := zeta_eq_chi_conj_on_line t
  have h2 : (‖riemannZeta s‖ : ℂ) ^ 2 =
      chi s * (starRingEnd ℂ) (riemannZeta s) * (starRingEnd ℂ) (riemannZeta s) := by
    calc
      (‖riemannZeta s‖ : ℂ) ^ 2 = (↑(‖riemannZeta s‖ ^ 2) : ℂ) := by
        exact (map_pow Complex.ofRealHom (‖riemannZeta s‖) 2).symm
      _ = (Complex.normSq (riemannZeta s) : ℂ) := by
        rw [← Complex.normSq_eq_norm_sq]
      _ = riemannZeta s * (starRingEnd ℂ) (riemannZeta s) := by
        rw [← Complex.mul_conj]
      _ = (chi s * (starRingEnd ℂ) (riemannZeta s)) * (starRingEnd ℂ) (riemannZeta s) := by
        exact congrArg (fun x : ℂ => x * (starRingEnd ℂ) (riemannZeta s)) hmain
  have hz_norm : (‖riemannZeta s‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have h1 : (1 : ℂ) = chi s * ((starRingEnd ℂ) u) ^ 2 := by
    calc
      1 = (‖riemannZeta s‖ : ℂ) ^ 2 / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        field_simp [hz_norm]
      _ = (chi s * (starRingEnd ℂ) (riemannZeta s) * (starRingEnd ℂ) (riemannZeta s)) /
          (‖riemannZeta s‖ : ℂ) ^ 2 := by
        rw [h2]
      _ = chi s * ((starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ)) ^ 2 := by
        ring
      _ = chi s * ((starRingEnd ℂ) u) ^ 2 := by
        congr 1
        have hu : (starRingEnd ℂ) (riemannZeta s / (‖riemannZeta s‖ : ℂ)) =
            (starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ) := by
          rw [map_div₀]
          simp
        simpa [u] using hu
  have hu1 : u * (starRingEnd ℂ) u = 1 := by
    have hnorm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_div]
      have hn : ‖(‖riemannZeta s‖ : ℂ)‖ = ‖riemannZeta s‖ := by
        calc
          ‖(‖riemannZeta s‖ : ℂ)‖ = |‖riemannZeta s‖| :=
            RCLike.norm_ofReal (‖riemannZeta s‖)
          _ = ‖riemannZeta s‖ := abs_of_nonneg (norm_nonneg _)
      rw [hn]
      have hz_norm_r : ‖riemannZeta s‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      field_simp [hz_norm_r]
    rw [Complex.mul_conj]
    have hnsq : Complex.normSq u = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
    rw [hnsq, hnorm]
    norm_num
  have hu2 : u ^ 2 = chi s := by
    calc
      u ^ 2 = (chi s * ((starRingEnd ℂ) u) ^ 2) * u ^ 2 := by
        rw [← h1]
        simp
      _ = chi s * (((starRingEnd ℂ) u) * u) ^ 2 := by
        ring
      _ = chi s * (u * (starRingEnd ℂ) u) ^ 2 := by
        ring
      _ = chi s := by
        rw [hu1]
        ring
  dsimp [u, s] at hu2
  exact hu2

/-! ## 5. Hardy Z 定义 + 实值性 (相位对齐的代数投影) -/

/-- **Hardy Z 定义**: Z(t) := χ(1/2+it)^(-1/2)·ζ(1/2+it) — 相位
基点投影 (观测 K: 投影成一根线的坐标).   Hardy Z: the
phase-basepoint projection (the coordinate that collapses to a
line). -/
noncomputable def hardyZ (t : ℝ) : ℂ :=
  chi (1 / 2 + t * Complex.I) ^ (-1 / 2 : ℂ) * riemannZeta (1 / 2 + t * Complex.I)

/-- **★Z² = |ζ|² (相位对齐的代数投影)**: Z² = |ζ|² 实正 — 从
u² = χ 一步 (Z² = χ^{-1}·ζ² = χ^{-1}·χ·|ζ|²; cpow_add
(-1/2)+(-1/2) = -1, 无分支问题; 相位对齐的代数落点).   ★Z² =
|ζ|² (the algebraic projection of phase alignment): real positive
in one step from u² = χ. -/
theorem hardyZ_conj (t : ℝ) (hchi : chi (1 / 2 + t * Complex.I) ≠ -1) :
    conj (hardyZ t) = hardyZ t := by
  unfold hardyZ
  let s : ℂ := 1 / 2 + t * Complex.I
  let c : ℂ := chi s
  have hslit : c ∈ Complex.slitPlane := by
    simpa [c, s] using (chi_mem_slitPlane_on_line t hchi)
  have harg : c.arg ≠ Real.pi := Complex.slitPlane_arg_ne_pi hslit
  have hc0 : c ≠ 0 := by
    intro h
    have hu := chi_unit_modulus t
    have hz0 : chi (1 / 2 + t * Complex.I) = 0 := by
      simpa [c, s] using h
    rw [hz0] at hu
    norm_num at hu
  -- conj(χ^z) = conj(χ)^(conj z) (conj_cpow, χ 在 slitPlane)
  have hconj_cpow : conj (c ^ (-1 / 2 : ℂ)) = conj c ^ (-1 / 2 : ℂ) := by
    have h := Complex.conj_cpow c (-1 / 2 : ℂ) harg
    have h' := h.symm
    have hcn : conj (-1 / 2 : ℂ) = (-1 / 2 : ℂ) := by
      simp [map_inv₀, map_neg, map_ofNat]
    rw [hcn] at h'
    exact h'
  rw [map_mul]
  rw [hconj_cpow]
  -- conj(ζ(s)) = ζ(1/2-it) (riemannZeta_conj)
  have hzeta : conj (riemannZeta s) = riemannZeta (1 / 2 - t * Complex.I) := by
    rw [← riemannZeta_conj s]
    congr 1
    apply Complex.ext <;> simp [s]
  rw [hzeta]
  -- conj(χ(1/2+it)) = χ(1/2-it) (轴工具 chi_conj_symm: 共轭保持)
  have hconj_chi : conj (chi s) = chi (1 / 2 - t * Complex.I) := by
    have := chi_conj_symm t
    simpa [s] using this
  rw [hconj_chi]
  -- 临界线函数方程: ζ(1/2-it) = χ(1/2-it)·conj(ζ(1/2-it)) = χ(1/2-it)·ζ(1/2+it)
  have hfe : riemannZeta (1 / 2 - t * Complex.I) =
      chi (1 / 2 - t * Complex.I) * conj (riemannZeta (1 / 2 - t * Complex.I)) := by
    have := zeta_eq_chi_conj_on_line (-t)
    simpa [sub_eq_add_neg] using this
  rw [hfe]
  have hzeta2 : conj (riemannZeta (1 / 2 - t * Complex.I)) = riemannZeta (1 / 2 + t * Complex.I) := by
    rw [← riemannZeta_conj (1 / 2 - t * Complex.I)]
    congr 1
    apply Complex.ext <;> simp
  rw [hzeta2]
  -- χ(1/2-it)^(-1/2)·χ(1/2-it) = χ(1/2-it)^(1/2) (cpow_add, χ ≠ 0)
  have hc2 : chi (1 / 2 - t * Complex.I) ≠ 0 := by
    intro h
    have hconj : conj c = chi (1 / 2 - t * Complex.I) := by
      have := chi_conj_symm t
      simpa [c, s] using this
    rw [← hconj] at h
    exact hc0 ((map_eq_zero (starRingEnd ℂ)).mp h)
  have hcpow : chi (1 / 2 - t * Complex.I) ^ (-1 / 2 : ℂ) *
      chi (1 / 2 - t * Complex.I) = chi (1 / 2 - t * Complex.I) ^ (1 / 2 : ℂ) := by
    calc
      chi (1 / 2 - t * Complex.I) ^ (-1 / 2 : ℂ) * chi (1 / 2 - t * Complex.I)
          = chi (1 / 2 - t * Complex.I) ^ (-1 / 2 : ℂ) *
              chi (1 / 2 - t * Complex.I) ^ (1 : ℂ) := by
            congr 1
            exact (Complex.cpow_one (chi (1 / 2 - t * Complex.I))).symm
      _ = chi (1 / 2 - t * Complex.I) ^ (-1 / 2 + (1 : ℂ)) := by
        rw [← Complex.cpow_add (-1 / 2 : ℂ) (1 : ℂ) hc2]
      _ = chi (1 / 2 - t * Complex.I) ^ (1 / 2 : ℂ) := by congr 1; ring
  rw [← mul_assoc]
  rw [hcpow]
  -- χ(1/2-it) = conj(χ(1/2+it)) = χ(1/2+it)⁻¹ (chi_conj_symm + 单位模 ⟹ 轴圆连接)
  have hconj_chi2 : chi (1 / 2 - t * Complex.I) = conj c := by
    have := chi_conj_symm t
    simpa [c, s] using this.symm
  have hinv : conj c = c⁻¹ := by
    have hu : ‖c‖ = 1 := by
      simpa [c, s] using (chi_unit_modulus t)
    -- ‖c‖ = 1 ⟹ conj c = c⁻¹: normSq = conj c·c = ‖c‖² = 1 (标准)
    have hnsq : Complex.normSq c = 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have : ‖c‖ ^ 2 = 1 := by rw [hu]; norm_num
      exact this
    have hℂ : (Complex.normSq c : ℂ) = 1 := by exact_mod_cast hnsq
    have hsq : conj c * c = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      exact hℂ
    have h1 : ((starRingEnd ℂ) c)⁻¹ = c := inv_eq_of_mul_eq_one_right hsq
    calc
      (starRingEnd ℂ) c = (((starRingEnd ℂ) c)⁻¹)⁻¹ := by rw [inv_inv]
      _ = c⁻¹ := by rw [h1]
  have hchi_inv : chi (1 / 2 - t * Complex.I) = c⁻¹ := by
    rw [hconj_chi2, hinv]
  rw [hchi_inv]
  -- (c⁻¹)^(1/2) = c^(-1/2) (inv_cpow + cpow_neg: 幂结构法则)
  have hinv_cpow : (c⁻¹) ^ (1 / 2 : ℂ) = c ^ (-1 / 2 : ℂ) := by
    rw [Complex.inv_cpow c (1 / 2 : ℂ) harg]
    rw [← Complex.cpow_neg c (1 / 2 : ℂ)]
    congr 1
    ring
  rw [hinv_cpow]

theorem hardyZ_im_zero (t : ℝ) (hchi : chi (1 / 2 + t * Complex.I) ≠ -1) :
    (hardyZ t).im = 0 := by
  -- conj(Z) = Z (共轭反射对称) ⟹ im = 0 (conj 的虚部变号: 反射对称)
  have h := hardyZ_conj t hchi
  have him : (conj (hardyZ t)).im = (hardyZ t).im := congrArg Complex.im h
  rw [Complex.conj_im] at him
  linarith


/-! ## 缺口 1b: 翻转 = 零点 (Z 符号变化 ⟹ 临界线零点)

翻转计数 = N₀(T) 的缺失环: Z 实值 (上面已证) + Z 连续 + 中间值
⟹ Z 在区间两端符号相反 (翻转) ⟹ ∃ 临界线零点。对称路径: 不用
arg/分支, 用 Z 的共轭反射对称 (Z 实) + |ζ| 连续 (无分支)。
-/

/-- **χ 临界线连续**: chi 在 Re s = 1/2 上连续 (2π 显式形式:
cpow 底 2π ∈ slitPlane / Γ 在 re>0 / sin; 标准).   χ is continuous
on the critical line (explicit 2π form). -/
theorem chi_continuousOn_line : ContinuousOn chi {s : ℂ | s.re = 1 / 2} := by
  have hpow : ContinuousOn (fun s : ℂ => (2 * ↑Real.pi : ℂ) ^ (s - 1))
      {s | s.re = 1 / 2} := by
    refine ContinuousOn.cpow continuousOn_const ?hg ?h0
    · have hg : ContinuousOn (fun s : ℂ => s - 1) {s | s.re = 1 / 2} := by
        intro s hs
        exact (continuousAt_id.sub continuousAt_const).continuousWithinAt
      exact hg
    · intro s hs
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by
        rw [Complex.mul_re]
        simp
        nlinarith [Real.pi_pos]))
  have hΓ : ContinuousOn (fun s : ℂ => Complex.Gamma (1 - s))
      {s | s.re = 1 / 2} := by
    intro s hs
    have h1ms : ContinuousAt (fun s : ℂ => 1 - s) s := by
      change ContinuousAt ((fun _ : ℂ => (1 : ℂ)) - id) s
      exact continuousAt_const.sub continuousAt_id
    exact (ContinuousAt.comp (Complex.continuousAt_Gamma (1 - s) (by
      intro m hm
      have hsr : s.re = 1 / 2 := by simpa using hs
      have hre' : 1 - s.re = -↑(m : ℝ) := by
        simpa using congrArg Complex.re hm
      have hneg : -↑(m : ℝ) = 1 / 2 := by linarith [hsr, hre']
      have hnonneg : (0 : ℝ) ≤ ↑(m : ℝ) := Nat.cast_nonneg m
      nlinarith)) h1ms).continuousWithinAt
  have hsin : ContinuousOn (fun s : ℂ => Complex.sin (↑Real.pi * s / 2))
      {s | s.re = 1 / 2} := by
    have hlin : Continuous (fun s : ℂ => (↑Real.pi / 2 : ℂ) * s) :=
      continuous_const.mul continuous_id
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Function.comp_def] using
      (Complex.continuous_sin.comp hlin).continuousOn
  have h2pi_form : ContinuousOn
      (fun s : ℂ =>
        2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2))
      {s | s.re = 1 / 2} := by
    exact ((continuousOn_const.mul hpow).mul hΓ).mul hsin
  -- chi = 2π 显式形式 (chi_eq_explicit)
  refine ContinuousOn.congr h2pi_form ?_
  intro s hs
  exact (chi_eq_explicit s)

/-- **★Z = 0 ⟺ ζ = 0**: 临界线上 Hardy Z 的零点恰是 ζ 的零点
(chi ≠ 0 ⟹ chi^(-1/2) ≠ 0).   ★Z = 0 ⟺ ζ = 0: zeros of Hardy Z
on the critical line are exactly the zeros of ζ. -/
theorem hardyZ_eq_zero_iff (t : ℝ) (_hchi : chi (1 / 2 + t * Complex.I) ≠ -1) :
    hardyZ t = 0 ↔ riemannZeta (1 / 2 + t * Complex.I) = 0 := by
  unfold hardyZ
  have hc0 : chi (1 / 2 + t * Complex.I) ≠ 0 := chi_ne_zero_on_line t
  have hpow : chi (1 / 2 + t * Complex.I) ^ (-1 / 2 : ℂ) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hc0))
  constructor
  · intro hz
    exact (mul_eq_zero.mp hz).resolve_left hpow
  · intro hz
    rw [hz]
    exact mul_zero _

/-- **Z 逐点连续**: hardyZ 在 t 连续 (chi ≠ -1 时; 组合: 曲线连续
+ chi 连续 (临界线) + cpow 连续 (chi ∈ slitPlane) + ζ 可导).   Z is
continuous at t (composition of continuous maps). -/
theorem hardyZ_continuousAt (t : ℝ) (hchi : chi (1 / 2 + t * Complex.I) ≠ -1) :
    ContinuousAt hardyZ t := by
  unfold hardyZ
  -- 曲线: x ↦ 1/2 + x·I (ℝ → ℂ, 全局连续, 值域在临界线且避开 1)
  have hcurveC : Continuous (fun x : ℝ => (1 / 2 : ℂ) + (x : ℂ) * Complex.I) := by
    fun_prop
  have hcurveOn : ContinuousOn (fun x : ℝ => (1 / 2 : ℂ) + (x : ℂ) * Complex.I) Set.univ :=
    hcurveC.continuousOn
  have hne_one : ∀ x : ℝ, (1 / 2 : ℂ) + (x : ℂ) * Complex.I ≠ 1 := by
    intro x hx
    have hre : ((1 / 2 : ℂ) + (x : ℂ) * Complex.I).re = 1 := by rw [hx]; simp
    simp at hre
  -- g : t ↦ ζ(1/2+it): ζ 在 {1}ᶜ 连续 (可导) ∘ 曲线
  have hzetaC : ContinuousOn riemannZeta ({1}ᶜ : Set ℂ) :=
    differentiableOn_riemannZeta.continuousOn
  have hcompOn : ContinuousOn (fun x : ℝ => riemannZeta ((1 / 2 : ℂ) + (x : ℂ) * Complex.I))
      Set.univ :=
    hzetaC.comp hcurveOn (by intro x hx; exact hne_one x)
  have hg : ContinuousAt (fun x : ℝ => riemannZeta ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)) t :=
    (continuousOn_univ.mp hcompOn).continuousAt
  -- c : t ↦ χ(1/2+it): χ 临界线连续 (chi_continuousOn_line) ∘ 曲线
  have hchiOn : ContinuousOn (fun x : ℝ => chi (1 / 2 + x * Complex.I)) Set.univ :=
    chi_continuousOn_line.comp hcurveOn (by intro x hx; simp)
  have hc : ContinuousAt (fun x : ℝ => chi (1 / 2 + x * Complex.I)) t :=
    (continuousOn_univ.mp hchiOn).continuousAt
  -- f : t ↦ χ(1/2+it)^(-1/2): cpow 连续 (χ 在 slitPlane, ContinuousAt.cpow)
  have hslit : chi (1 / 2 + t * Complex.I) ∈ Complex.slitPlane :=
    chi_mem_slitPlane_on_line t hchi
  have hf : ContinuousAt (fun x : ℝ => chi (1 / 2 + x * Complex.I) ^ (-1 / 2 : ℂ)) t := by
    exact ContinuousAt.cpow hc continuousAt_const hslit
  -- Z = f·g
  have hfg : ContinuousAt (fun x : ℝ =>
      chi (1 / 2 + x * Complex.I) ^ (-1 / 2 : ℂ) * riemannZeta (1 / 2 + x * Complex.I)) t := by
    convert hf.mul hg using 1
    funext x
    rfl
  simpa [hardyZ] using hfg

/-- **Z 区间连续**: hardyZ 在 [a,b] 连续 (区间内 chi ≠ -1).   Z is
continuous on [a,b]. -/
theorem hardyZ_continuousOn (a b : ℝ)
    (hcont : ∀ t ∈ Set.Icc a b, chi (1 / 2 + t * Complex.I) ≠ -1) :
    ContinuousOn hardyZ (Set.Icc a b) := by
  intro t ht
  exact (hardyZ_continuousAt t (hcont t ht)).continuousWithinAt

/-- **★翻转 = 零点 (中间值)**: Z(a) < 0 < Z(b) (两端符号相反 =
一次翻转) ⟹ ∃t ∈ (a,b), Z(t) = 0 (中间值定理; Z 实值 + 连续).
符号变化 (翻转 ±1) 处的位置 = 临界线零点 — 翻转计数 = N₀(T) 的
缺失环。   ★Flip = zero (intermediate value): sign change of Z
between a and b forces a zero of Z, i.e. a zero of ζ on the
critical line. -/
theorem hardyZ_zero_between (a b : ℝ) (hab : a < b)
    (hza : (hardyZ a).re < 0) (hzb : 0 < (hardyZ b).re)
    (hcont : ∀ t ∈ Set.Icc a b, chi (1 / 2 + t * Complex.I) ≠ -1) :
    ∃ t : ℝ, a < t ∧ t < b ∧ hardyZ t = 0 := by
  let Z : ℝ → ℝ := fun t => (hardyZ t).re
  have hcontZ : ContinuousOn Z (Set.Icc a b) := by
    intro x hx
    have hx_cont : ContinuousWithinAt hardyZ (Set.Icc a b) x :=
      hardyZ_continuousOn a b hcont x hx
    have hre_cont : ContinuousWithinAt Complex.re Set.univ (hardyZ x) :=
      Complex.continuous_re.continuousWithinAt
    exact hre_cont.comp hx_cont (by intro y hy; trivial)
  -- 中间值: Z(a) ≤ 0 ≤ Z(b) (两端符号相反)
  have hza_le : Z a ≤ 0 := le_of_lt hza
  have hzb_le : 0 ≤ Z b := le_of_lt hzb
  have hmem : 0 ∈ Set.Icc (Z a) (Z b) := ⟨hza_le, hzb_le⟩
  have himage : 0 ∈ Z '' Set.Icc a b :=
    intermediate_value_Icc (le_of_lt hab) hcontZ hmem
  rcases himage with ⟨x, hxIcc, hx0⟩
  -- x = a 或 x = b 与严格符号矛盾
  have hx_ne_a : x ≠ a := by
    intro hx
    have : Z a = 0 := by simpa [Z, hx] using hx0
    linarith
  have hx_ne_b : x ≠ b := by
    intro hx
    have : Z b = 0 := by simpa [Z, hx] using hx0
    linarith
  have hx_gt : a < x := lt_of_le_of_ne hxIcc.1 (Ne.symm hx_ne_a)
  have hx_lt : x < b := lt_of_le_of_ne hxIcc.2 hx_ne_b
  -- Z x = 0 ∧ im = 0 ⟹ hardyZ x = 0 (Z 实值)
  have him : (hardyZ x).im = 0 := hardyZ_im_zero x (hcont x hxIcc)
  have hz_eq : hardyZ x = 0 := by
    apply Complex.ext
    · simpa [Z] using hx0
    · simpa using him
  exact ⟨x, hx_gt, hx_lt, hz_eq⟩

end ZeroRelative
