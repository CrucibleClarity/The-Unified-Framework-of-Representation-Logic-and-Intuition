/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# 0pat Exercise XXXVII: The Riemann Direction, Unified — 完整隔离版本

iso 分块 (zeta_*_iso.lean, 每块独立编译通过) 拼接为单文件完整证明:
声明级去重 (同名定理保留首现; zetaUnit ℝ 版重命名 zetaUnitOnLine),
只 import Mathlib。Hardy Z 见 HardyZ.lean (独立自包含)。0 error 0 sorry。
-/

noncomputable section
open Complex Function FormalMultilinearSeries Set circleIntegral
open Metric
open scoped Topology
open Complex
open Filter
open scoped Topology BigOperators
open scoped Topology ComplexConjugate
open scoped BigOperators
open HurwitzZeta
open Set
open Filter Function Set

namespace RiemannUnifiedObservation

/-- **对数导数分解**: f = (z-z₀)·g ⟹ f'/f = 1/(z-z₀) + g'/g
    (乘积求导: f' = g + (z-z₀)·g' ⟹ f'/f = g/f + (z-z₀)g'/f
    = 1/(z-z₀) + g'/g, 在 z ≠ z₀ 且 g ≠ 0 处)。 -/
theorem logDeriv_decomposition {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : ∀ z, f z = (z - z₀) * g z) (hg : DifferentiableAt ℂ g z)
    (hz : z ≠ z₀) (hgz : g z ≠ 0) :
    deriv f z / f z = (z - z₀)⁻¹ + deriv g z / g z := by
  -- f' = g + (z-z₀)·g' (乘积求导)
  have hderiv : deriv f z = g z + (z - z₀) * deriv g z := by
    have hfg : f = fun w => (w - z₀) * g w := by
      funext w
      exact hf w
    rw [hfg]
    have hd : deriv (fun w : ℂ => w - z₀) z = 1 := by
      simp
    have hdm : deriv (fun w : ℂ => (w - z₀) * g w) z =
        deriv (fun w : ℂ => w - z₀) z * g z + (z - z₀) * deriv g z := by
      have hc : DifferentiableAt ℂ (fun w : ℂ => w - z₀) z := by fun_prop
      have hdm0 := deriv_mul (𝕜 := ℂ) hc hg
      -- hdm0 : deriv ((fun w => w - z₀) * g) z = deriv (fun w => w-z₀) z * g z + ...
      calc
        deriv (fun w : ℂ => (w - z₀) * g w) z = deriv ((fun w : ℂ => w - z₀) * g) z := by
          congr 1
        _ = deriv (fun w : ℂ => w - z₀) z * g z + (z - z₀) * deriv g z := hdm0
    rw [hdm, hd]
    ring
  -- f = (z-z₀)·g, 除:
  rw [hderiv, hf z]
  -- (g + (z-z₀)g') / ((z-z₀)·g) = 1/(z-z₀) + g'/g
  field_simp [hz, hgz]

/-- **参数原理 (单简单零点, 圆路径)**: f 在闭圆盘解析, 唯一简单零点
    z₀ 在内部, 边界无零点 ⟹ ∮_{C(c,R)} f'/f = 2πi。
    证明: 局部 f = (z-z₀)g (g(z₀) ≠ 0); 环域上 ∮_{C(c,R)} = ∮_{C(z₀,r)};
    ∮_{C(z₀,r)} f'/f = ∮ 1/(z-z₀) + ∮ g'/g = 2πi + 0。 -/
theorem circle_argument_principle_simple_zero {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R))
    (hfz₀ : f z₀ = 0) (hf' : deriv f z₀ ≠ 0)
    (hfne : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z ≠ 0) :
    (∮ z in C(z₀, R / 2), deriv f z / f z) = 2 * ↑Real.pi * I := by
  let g : ℂ → ℂ := dslope f z₀
  -- f = (z-z₀)·g 处处 (f(z₀) = 0: (z-z₀)·dslope = f z - f z₀)
  have hfg : ∀ z, f z = (z - z₀) * g z := by
    intro z
    have hd := sub_smul_dslope f z₀ z
    have : f z = (z - z₀) * dslope f z₀ z := by
      simpa [smul_eq_mul, hfz₀] using hd.symm
    simpa [g] using this
  -- g(z₀) = deriv f z₀ ≠ 0
  have hgz₀ : g z₀ ≠ 0 := by
    simpa [g, dslope_same] using hf'
  -- g ≠ 0 于开球 (去心由 f ≠ 0, 圆心由 hgz₀)
  have hgne : ∀ z ∈ ball z₀ R, g z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = z₀
    · subst z
      exact hgz₀
    · have hg : g z = f z / (z - z₀) := by
        dsimp [g]
        have hd0 := dslope_of_ne f hz0
        rw [hd0]
        simp [slope, hfz₀, div_eq_mul_inv, mul_comm]
      rw [hg]
      exact div_ne_zero (hfne z hz hz0) (sub_ne_zero.mpr hz0)
  -- f 解析于开球 ⟹ g 解析于开球
  have hf_ana : AnalyticOn ℂ f (ball z₀ R) := hf.analyticOn isOpen_ball
  have hg_ana : AnalyticOn ℂ g (ball z₀ R) := by
    intro z hz
    by_cases hz0 : z = z₀
    · subst z
      rcases (hf_ana.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))) with ⟨p, hp⟩
      -- dslope 保持解析 (has_fpower_series_iterate_dslope_fslope)
      have hds : HasFPowerSeriesAt (dslope f z₀) (fslope^[1] p) z₀ := by
        -- swap dslope z₀ f = dslope f z₀ (swap 交换 dslope 的第 2/3 参数)
        simpa [g, swap] using (hp.has_fpower_series_iterate_dslope_fslope 1)
      exact hds.analyticAt.analyticWithinAt
    · -- z ≠ z₀: g 与 f/(·-z₀) 邻域相等, 后者解析 (f 解析 / 非零线性)
      have hg_eq : g =ᶠ[𝓝 z] fun w => f w / (w - z₀) := by
        filter_upwards [eventually_ne_nhds hz0] with w hw
        dsimp [g]
        have hd0 := dslope_of_ne f hw
        rw [hd0]
        simp [slope, hfz₀, div_eq_mul_inv, mul_comm]
      have hid : AnalyticAt ℂ (fun w : ℂ => w - z₀) z := by
        -- id - const: 多项式解析 (恒等与常数)
        simpa [show (fun w : ℂ => w - z₀) = _root_.id - fun _ : ℂ => z₀ by funext w; rfl]
          using ((analyticAt_id (𝕜 := ℂ) (E := ℂ) (z := z)).sub
            (analyticAt_const (𝕜 := ℂ) (F := ℂ) (x := z) (v := z₀)))
      have hquot : AnalyticAt ℂ (fun w : ℂ => f w / (w - z₀)) z :=
        (hf_ana.analyticAt (isOpen_ball.mem_nhds hz)).div hid (sub_ne_zero.mpr hz0)
      exact ((analyticAt_congr hg_eq).mpr hquot).analyticWithinAt
  -- g 可导于开球 (解析 ⟹ 可导)
  have hg_diff : DifferentiableOn ℂ g (ball z₀ R) := hg_ana.differentiableOn
  -- 圆周上分解: f'/f = (z-z₀)⁻¹ + g'/g
  have hfun : EqOn (fun z => deriv f z / f z)
      (fun z => (z - z₀)⁻¹ + deriv g z / g z) (sphere z₀ (R / 2)) := by
    intro z hz
    have hzball : z ∈ ball z₀ R := by
      -- dist z z₀ = R/2 < R
      exact mem_ball.mpr (by
        have hd : dist z z₀ = R / 2 := by simpa [sphere] using hz
        linarith)
    have hz0 : z ≠ z₀ := by
      -- dist z z₀ = R/2 > 0
      intro h
      have : dist z z₀ = 0 := by rw [h]; simp
      linarith [show dist z z₀ = R / 2 by simpa [sphere] using hz, hR]
    exact logDeriv_decomposition hfg
      ((hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)).differentiableAt) hz0 (hgne z hzball)
  -- ∮ f'/f = ∮ 1/(z-z₀) + ∮ g'/g (积分线性)
  have hsplit : (∮ z in C(z₀, R / 2), deriv f z / f z) =
      (∮ z in C(z₀, R / 2), (z - z₀)⁻¹) + (∮ z in C(z₀, R / 2), deriv g z / g z) := by
    calc
      (∮ z in C(z₀, R / 2), deriv f z / f z) =
          ∮ z in C(z₀, R / 2), ((z - z₀)⁻¹ + deriv g z / g z) := by
        rw [circleIntegral.integral_congr (by positivity : (0 : ℝ) ≤ R / 2) hfun]
      _ = (∮ z in C(z₀, R / 2), (z - z₀)⁻¹) +
          (∮ z in C(z₀, R / 2), deriv g z / g z) := by
        rw [circleIntegral.integral_add]
        · -- (z-z₀)⁻¹ 连续于圆周 ⟹ 可积
          refine ContinuousOn.circleIntegrable' ?_
          intro z hz
          -- (fun z => (z - z₀)⁻¹) 连续于 z (z ≠ z₀)
          have hz_ne : (fun w : ℂ => w - z₀) z ≠ 0 := by
            change z - z₀ ≠ 0
            intro hz_eq  -- hz_eq : z - z₀ = 0
            have hz0 : z = z₀ := sub_eq_zero.mp hz_eq
            have hd : dist z z₀ = R / 2 := by
              have hz' : dist z z₀ = |R / 2| := by simpa [sphere] using hz
              rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R / 2)] at hz'
            rw [hz0] at hd
            simp at hd
            linarith
          exact ((continuousAt_id.sub continuousAt_const).inv₀ hz_ne).continuousWithinAt
        · -- g'/g 连续于圆周 ⟹ 可积
          refine ContinuousOn.circleIntegrable' ?_
          intro z hz
          -- g 解析 ⟹ g'/g 解析 ⟹ 连续
          have hzball : z ∈ ball z₀ R := by
            have hd : dist z z₀ = R / 2 := by
              have hz' : dist z z₀ = |R / 2| := by simpa [sphere] using hz
              rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R / 2)] at hz'
            exact mem_ball.mpr (by linarith)
          have hd_ana : AnalyticAt ℂ (fun w => deriv g w / g w) z :=
            ((hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)).deriv).div
              (hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)) (hgne z hzball)
          exact hd_ana.continuousAt.continuousWithinAt
  -- ∮ 1/(z-z₀) = 2πi
  have hmain : (∮ z in C(z₀, R / 2), (z - z₀)⁻¹) = 2 * ↑Real.pi * I := by
    -- integral_sub_inv_of_mem_ball: z₀ ∈ ball z₀ (R/2)
    exact integral_sub_inv_of_mem_ball (c := z₀) (w := z₀) (R := R / 2)
      (mem_ball_self (div_pos hR (by norm_num)))
  -- ∮ g'/g = 0 (g'/g 解析于小闭圆盘, Goursat)
  have hzero : (∮ z in C(z₀, R / 2), deriv g z / g z) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable (c := z₀) (R := R / 2)
      (s := ∅) (f := fun z => deriv g z / g z)
    · -- 0 ≤ R/2
      positivity
    · -- s 可数
      simp
    · -- ContinuousOn (fun z => deriv g z / g z) (closedBall z₀ (R/2))
      have hdg_ana : AnalyticOn ℂ (deriv g) (ball z₀ R) := fun z hz =>
        (hg_ana.analyticAt (isOpen_ball.mem_nhds hz)).deriv.analyticWithinAt
      have hsub : closedBall z₀ (R / 2) ⊆ ball z₀ R := by
        intro z hz
        exact mem_ball.mpr (by
          have hd : dist z z₀ ≤ R / 2 := (mem_closedBall.mp hz)
          linarith)
      have hdg_cont : ContinuousOn (deriv g) (closedBall z₀ (R / 2)) :=
        hdg_ana.continuousOn.mono hsub
      have hg_cont : ContinuousOn g (closedBall z₀ (R / 2)) :=
        hg_ana.continuousOn.mono hsub
      have hg_inv : ContinuousOn (fun z => (g z)⁻¹) (closedBall z₀ (R / 2)) :=
        hg_cont.inv₀ (fun z hz => hgne z (hsub hz))
      have hmul : ContinuousOn (deriv g * fun z => (g z)⁻¹) (closedBall z₀ (R / 2)) :=
        hdg_cont.mul hg_inv
      have hfun_eq : (deriv g * fun z => (g z)⁻¹) = fun z => deriv g z * (g z)⁻¹ := by
        funext z
        rfl
      simpa [div_eq_mul_inv, hfun_eq] using hmul
    · -- hd: 开球内 (去心) g'/g 可导
      intro z hz
      have hzball : z ∈ ball z₀ R := by
        have hd : dist z z₀ < R / 2 := (mem_ball.mp hz.1)
        exact mem_ball.mpr (by linarith)
      have hd_ana : AnalyticAt ℂ (fun w => deriv g w / g w) z :=
        ((hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)).deriv).div
          (hg_ana.analyticAt (isOpen_ball.mem_nhds hzball)) (hgne z hzball)
      exact hd_ana.differentiableAt
  -- 组合: 2·↑π·I + 0
  rw [hsplit, hmain, hzero]
  ring

/-- **相位-计数恒等式**: 参数原理的积分形式 — 绕闭合路径的相位变化
    = 2πi·(内部零点数)。单零点: ∮ f'/f = 2πi ⟺ 一个零点。 -/
theorem zero_count_formula {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R))
    (hfz₀ : f z₀ = 0) (hf' : deriv f z₀ ≠ 0)
    (hfne : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z ≠ 0) :
    (∮ z in C(z₀, R / 2), deriv f z / f z) / (2 * ↑Real.pi * I) = 1 := by
  rw [circle_argument_principle_simple_zero hR hf hfz₀ hf' hfne]
  -- (2πi)/(2πi) = 1
  have hne : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
    have hπ : (↑Real.pi : ℂ) ≠ 0 := by
      intro h
      exact Real.pi_ne_zero (Complex.ofReal_eq_zero.mp h)
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hπ)
      (by norm_num : (I : ℂ) ≠ 0)
  exact div_self hne


/-- 临界线 = i 与 1+i 的垂直平分线 (基点 i 坐标的等距判据):
    Re z = 1/2 ⟺ ‖z-i‖ = ‖z-(1+i)‖。 -/
theorem critical_line_equidistant_basepoint_i (z : ℂ) :
    z.re = 1 / 2 ↔ ‖z - Complex.I‖ = ‖z - (1 + Complex.I)‖ := by
  constructor
  · intro hre
    -- 平方相等 (normSq 展开 + hre)
    have hsq : ‖z - Complex.I‖ ^ 2 = ‖z - (1 + Complex.I)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      rw [hre]
      ring
    -- 非负 ⟹ 平方等式到等式
    have habs : |‖z - Complex.I‖| = |‖z - (1 + Complex.I)‖| :=
      (sq_eq_sq_iff_abs_eq_abs ‖z - Complex.I‖ ‖z - (1 + Complex.I)‖).mp hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  · intro h
    -- 平方相等
    have hsq : ‖z - Complex.I‖ ^ 2 = ‖z - (1 + Complex.I)‖ ^ 2 := by rw [h]
    have hns : Complex.normSq (z - Complex.I) = Complex.normSq (z - (1 + Complex.I)) := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    -- 展开 re/im ⟹ (z.re-1)² = z.re² ⟹ z.re = 1/2
    rw [Complex.normSq_apply, Complex.normSq_apply] at hns
    simp at hns
    nlinarith

/-- T 坐标 (基点 i): 临界线 = 单位圆。T(z) = 1/(z-i) - 1
    (recip 中心 = 复平面基点 i, 平移 -1 消圆心):
    Re z = 1/2 ⟺ ‖1/(z-i) - 1‖ = 1。 -/
theorem recip_basepoint_i_on_unit_circle (z : ℂ) (hz : z ≠ Complex.I) :
    ‖1 / (z - Complex.I) - 1‖ = 1 ↔ z.re = 1 / 2 := by
  -- 1/(z-i) - 1 = -(z-(1+i))/(z-i) (代数)
  have hrewrite : 1 / (z - Complex.I) - 1 = -((z - (1 + Complex.I)) / (z - Complex.I)) := by
    field_simp [sub_ne_zero.mpr hz]
    ring
  have hne : ‖z - Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  -- |1/(z-i)-1| = |z-(1+i)|/|z-i| = 1 ⟺ |z-(1+i)| = |z-i| (等距)
  rw [hrewrite, norm_neg, norm_div, div_eq_one_iff_eq hne]
  rw [eq_comm]
  exact (critical_line_equidistant_basepoint_i z).symm


/-- 仿射基点移动保持临界线的直线性: Re(a·z + c) = 1/2 是直线
    (方向 d = i·ā ≠ 0, 过点 p = (1/2 - Re c)·ā/|a|²)。 -/
theorem affine_image_critical_line_is_line (a c : ℂ) (ha : a ≠ 0) :
    ∃ (p : ℂ) (d : ℂ), d ≠ 0 ∧
      {z : ℂ | (a * z + c).re = 1 / 2} = {p + s • d | s : ℝ} := by
  let d : ℂ := Complex.I * (starRingEnd ℂ a)
  let p : ℂ := ((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2
  have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hn_c : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
  have hnorm_c : (‖a‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn_c
  -- a·p = (1/2 - Re c) 是实数 (a·ā = |a|² 对消)
  have hapeq : a * (((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2)
      = ((1 / 2 : ℝ) - c.re : ℂ) := by
    calc
      a * (((1 / 2 : ℝ) - c.re) * (starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2)
          = ((1 / 2 : ℝ) - c.re) * (a * starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2 := by ring
      _ = ((1 / 2 : ℝ) - c.re) * (Complex.normSq a : ℂ) / (‖a‖ : ℂ) ^ 2 := by
        rw [Complex.mul_conj]
      _ = ((1 / 2 : ℝ) - c.re) * ((‖a‖ : ℂ) ^ 2) / ((‖a‖ : ℂ) ^ 2) := by
        rw [Complex.normSq_eq_norm_sq]
        norm_num
      _ = ((1 / 2 : ℝ) - c.re : ℂ) := by
        field_simp [hnorm_c, hn_c]
  -- a⁻¹ = ā / |a|²
  have hinv : a⁻¹ = starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2 := by
    have hmul : a * (starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) = 1 := by
      calc
        a * (starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) = (a * starRingEnd ℂ a) / (‖a‖ : ℂ) ^ 2 := by ring
        _ = (Complex.normSq a : ℂ) / (‖a‖ : ℂ) ^ 2 := by rw [Complex.mul_conj]
        _ = (‖a‖ : ℂ) ^ 2 / (‖a‖ : ℂ) ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]
          norm_num
        _ = 1 := by
          field_simp [hnorm_c, hn_c]
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  refine ⟨p, d, ?_, ?_⟩
  · -- d ≠ 0: I·ā ≠ 0 (I ≠ 0, ā ≠ 0)
    have hconj : starRingEnd ℂ a ≠ 0 := by
      intro h
      have h' := congrArg (starRingEnd ℂ) h
      have : a = 0 := by simpa using h'
      exact ha this
    exact mul_ne_zero (by norm_num : Complex.I ≠ 0) hconj
  · ext z
    constructor
    · -- Re(az+c) = 1/2 ⟹ z = p + s·d (w = a(z-p) 纯虚 ⟹ z-p = (w.im/|a|²)·d)
      intro hz
      let w : ℂ := a * (z - p)
      have haz_re : (a * z).re = 1 / 2 - c.re := by
        have hz' : (a * z).re + c.re = 1 / 2 := by
          simpa [Complex.add_re, Complex.ofReal_re] using hz
        linarith
      have hap_re : (a * p).re = 1 / 2 - c.re := by
        have hpeq : a * p = ((1 / 2 : ℝ) - c.re : ℂ) := by
          dsimp [p]
          exact hapeq
        rw [hpeq]
        simp [Complex.ofReal_re]
      have hwre : w.re = 0 := by
        dsimp [w]
        have hsub : a * (z - p) = a * z - a * p := by ring
        rw [hsub, Complex.sub_re, haz_re, hap_re]
        ring
      have hw_pure : w = w.im * Complex.I := by
        apply Complex.ext <;> simp [hwre]
      have hzpe : z - p = a⁻¹ * w := by
        calc
          z - p = 1 * (z - p) := by simp
          _ = (a⁻¹ * a) * (z - p) := by rw [inv_mul_cancel₀ ha]
          _ = a⁻¹ * (a * (z - p)) := by ring
      -- wim = w.im (避免 rw 污染投影)
      let wim : ℝ := w.im
      have hw_pure' : w = wim * Complex.I := by
        dsimp [wim]
        exact hw_pure
      have hzpd : z - p = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
        rw [hzpe, hw_pure']
        -- 乘法形式: a⁻¹·(wim·I) = (wim:ℂ)/|a|²·(I·ā)
        have hm : a⁻¹ * (wim * Complex.I)
            = (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a) := by
          calc
            a⁻¹ * (wim * Complex.I) = wim * (a⁻¹ * Complex.I) := by ring
            _ = wim * (Complex.I * starRingEnd ℂ a / (‖a‖ : ℂ) ^ 2) := by
              rw [hinv]
              ring
            _ = (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a) := by
              ring
        -- 转成标量形式: (wim:ℂ)/|a|²·x = (wim/|a|² : ℝ) • x
        have hm' : (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a)
            = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
          calc
            (wim : ℂ) / (‖a‖ : ℂ) ^ 2 * (Complex.I * starRingEnd ℂ a)
                = ((wim / ‖a‖ ^ 2 : ℝ) : ℂ) * (Complex.I * starRingEnd ℂ a) := by
                  have hden : (‖a‖ : ℂ) ^ 2 = ((‖a‖ ^ 2 : ℝ) : ℂ) := by norm_num
                  rw [hden]
                  -- ↑wim / ↑(‖a‖²) · x = ↑(wim/‖a‖²) · x: 先分离共同因子 x
                  congr 1
                  norm_num
            _ = (wim / ‖a‖ ^ 2) • (Complex.I * starRingEnd ℂ a) := by
                  simp [smul_eq_mul]
        exact hm.trans hm'
      refine ⟨wim / ‖a‖ ^ 2, ?_⟩
      rw [← hzpd]
      ring
    · -- z = p + s·d ⟹ Re(az+c) = 1/2 (s·d 纯虚 + ap 实)
      rintro ⟨s, rfl⟩
      have hsd : (a * (s • (Complex.I * starRingEnd ℂ a))).re = 0 := by
        -- a·(s·(I·ā)) = s·(I·(a·ā)) = s·(I·|a|²) 纯虚
        calc
          (a * (s • (Complex.I * starRingEnd ℂ a))).re
              = (a * ((s : ℂ) * (Complex.I * starRingEnd ℂ a))).re := by
                simp
          _ = ((s : ℂ) * (Complex.I * (a * starRingEnd ℂ a))).re := by
                congr 1
                ring
          _ = ((s : ℂ) * (Complex.I * (Complex.normSq a : ℂ))).re := by
                rw [Complex.mul_conj]
          _ = 0 := by
                simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      calc
        (a * (p + s • (Complex.I * starRingEnd ℂ a)) + c).re
            = (a * p + a * (s • (Complex.I * starRingEnd ℂ a)) + c).re := by
              rw [mul_add]
        _ = (a * p + c).re := by
              -- (a·(s•d)).re = 0 (hsd): 展开 re 后替换
              calc
                (a * p + a * (s • (Complex.I * starRingEnd ℂ a)) + c).re
                    = (a * p).re + (a * (s • (Complex.I * starRingEnd ℂ a))).re + c.re := by
                      simp [Complex.add_re]
                _ = (a * p).re + 0 + c.re := by rw [hsd]
                _ = (a * p + c).re := by
                      simp [Complex.add_re]
        _ = 1 / 2 := by
          have hpeq : a * p = ((1 / 2 : ℝ) - c.re : ℂ) := by
            dsimp [p]
            exact hapeq
          rw [hpeq]
          simp [Complex.add_re, Complex.ofReal_re]


/-- 基点 1 (临界线圆圆心) 坐标下的在线判据:
    z = 1+w 在临界线上 ⟺ w 到 0 (反演中心) 与到 -1 (圆上点) 等距.
    临界线圆 |z-1| = 1 在基点 1 坐标下 = 单位圆 |w| = 1. -/
theorem on_line_iff_equidistant_base_one (w : ℂ) :
    (1 + w).re = 1 / 2 ↔ ‖w‖ = ‖1 + w‖ := by
  constructor
  · intro h
    have hre : w.re = -1 / 2 := by
      have : (1 + w).re = 1 + w.re := by simp [Complex.add_re, Complex.ofReal_re]
      linarith
    -- ‖w‖² = ‖1+w‖² (normSq 展开 + hre)
    have hsq : ‖w‖ ^ 2 = ‖1 + w‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      rw [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
      rw [hre]
      ring
    -- 非负 ⟹ 从平方等式到等式
    have habs : |‖w‖| = |‖1 + w‖| :=
      (sq_eq_sq_iff_abs_eq_abs ‖w‖ ‖1 + w‖).mp hsq
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  · intro h
    have hsq : ‖w‖ ^ 2 = ‖1 + w‖ ^ 2 := by rw [h]
    have hns : Complex.normSq w = Complex.normSq (1 + w) := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    have hre : w.re = -1 / 2 := by
      rw [Complex.normSq_apply, Complex.normSq_apply,
        Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im] at hns
      nlinarith
    have : (1 + w).re = 1 + w.re := by simp [Complex.add_re, Complex.ofReal_re]
    linarith


/-- 2^s 沿临界线显式: 2^(1/2+it) = exp(ln 2 / 2) · (cos(t·ln 2) + i·sin(t·ln 2))。
    相位 = t·ln 2 (线性), 模 = 2^(1/2)。 -/
theorem cpow_two_on_line_explicit (t : ℝ) :
    (2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (Real.log 2 / 2) : ℂ) * (Real.cos (t * Real.log 2) : ℂ)
        + (Real.exp (Real.log 2 / 2) : ℂ) * (Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  have hdecomp : (Real.log 2 : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = ((Real.log 2 / 2 : ℝ) : ℂ) + ((t * Real.log 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring

/-- π^(s-1) 沿临界线显式: π^(-1/2+it) = exp(-ln π / 2) · (cos(t·ln π) + i·sin(t·ln π))。
    相位 = t·ln π (线性), 模 = π^(-1/2)。 -/
theorem cpow_pi_on_line_explicit (t : ℝ) :
    (↑Real.pi : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (-Real.log Real.pi / 2) : ℂ) * (Real.cos (t * Real.log Real.pi) : ℂ)
        + (Real.exp (-Real.log Real.pi / 2) : ℂ) * (Real.sin (t * Real.log Real.pi) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
  have hlog : Complex.log (↑Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
    exact (Complex.ofReal_log (le_of_lt Real.pi_pos)).symm
  rw [hlog]
  have hdecomp : (Real.log Real.pi : ℂ) * (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = ((-Real.log Real.pi / 2 : ℝ) : ℂ) + ((t * Real.log Real.pi : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring

/-- sin(πs/2) 沿临界线显式 (s = 1/2+it):
    sin(π/4 + iπt/2) = sin(π/4)·cosh(πt/2) + i·cos(π/4)·sinh(πt/2)。
    实部 = sin(π/4)·cosh(πt/2) > 0 恒正 ⟹ arg = arctan(tanh(πt/2))。 -/
theorem sin_pi_quarter_add_mul_I (t : ℝ) :
    Complex.sin (↑Real.pi / 4 + (t : ℂ) * ↑Real.pi / 2 * Complex.I)
      = Complex.sin (↑Real.pi / 4) * Complex.cosh ((Real.pi / 2 * t : ℝ) : ℂ)
        + Complex.cos (↑Real.pi / 4) * Complex.sinh ((Real.pi / 2 * t : ℝ) : ℂ) * Complex.I := by
  have h := Complex.sin_add_mul_I (↑(Real.pi / 4) : ℂ) ((Real.pi / 2 * t : ℝ) : ℂ)
  have hL : ↑Real.pi / 4 + (t : ℂ) * ↑Real.pi / 2 * Complex.I
      = ↑(Real.pi / 4) + ↑(Real.pi / 2 * t) * Complex.I := by
    norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add]
    ring
  rw [hL]
  simpa using h


/-- χ 的平移递推 (数字层): χ(s+2) = -4π²/(s(s+1))·χ(s)。
    χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2)。s ≠ 0, -1 (Γ 递推与分母)。 -/
theorem chi_translation_two (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    2 * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) * Complex.sin (↑Real.pi * (s + 2) / 2)
      = -4 * (↑Real.pi) ^ 2 / (s * (s + 1)) * (2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)) := by
  -- (2π)^{s+1} = (2π)^{s-1}·(2π)²
  have hpow : (2 * ↑Real.pi : ℂ) ^ (s + 1) = (2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (2 : ℂ) := by
    rw [← Complex.cpow_add (s - 1) 2 (by exact_mod_cast (mul_pos (by norm_num) Real.pi_pos).ne')]
    congr 1
    ring
  have hpow2 : (2 * ↑Real.pi : ℂ) ^ (2 : ℂ) = 4 * (↑Real.pi) ^ 2 := by
    have hc2 : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
    rw [hc2, Complex.cpow_natCast]
    ring
  -- sin(π(s+2)/2) = -sin(πs/2)
  have hsin : Complex.sin (↑Real.pi * (s + 2) / 2) = -Complex.sin (↑Real.pi * s / 2) := by
    have harg : ↑Real.pi * (s + 2) / 2 = ↑Real.pi * s / 2 + ↑Real.pi := by ring
    rw [harg, Complex.sin_add_pi]
  -- Γ(-1-s) = Γ(1-s)/(s(s+1)): Gamma_add_one 两次 (需 -s ≠ 0, -1-s ≠ 0)
  have hG1 : Complex.Gamma (1 - s) = (-s) * Complex.Gamma (-s) := by
    have hne : -s ≠ 0 := by
      intro h
      apply hs0
      exact neg_eq_zero.mp h
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Complex.Gamma_add_one (-s) hne)
  have hG2 : Complex.Gamma (-s) = (-1 - s) * Complex.Gamma (-1 - s) := by
    have hne : -1 - s ≠ 0 := by
      intro h
      apply hs1
      -- -1 - s = 0 ⟹ s = -1
      have h' : (s + 1 : ℂ) = 0 := by
        have : s + 1 = -(-1 - s) := by ring
        rw [this, h]
        norm_num
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h']
        _ = -1 := by norm_num
    have hg := Complex.Gamma_add_one (-1 - s) hne
    have harg : (-1 - s) + 1 = -s := by ring
    rw [harg] at hg
    exact hg
  have hrel : Complex.Gamma (1 - s) = s * (s + 1) * Complex.Gamma (-1 - s) := by
    calc
      Complex.Gamma (1 - s) = (-s) * Complex.Gamma (-s) := hG1
      _ = (-s) * ((-1 - s) * Complex.Gamma (-1 - s)) := by rw [hG2]
      _ = s * (s + 1) * Complex.Gamma (-1 - s) := by ring
  have hs' : s * (s + 1) ≠ 0 := by
    exact mul_ne_zero hs0 (by
      intro h
      apply hs1
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h]
        _ = -1 := by norm_num)
  have hG : Complex.Gamma (-1 - s) = Complex.Gamma (1 - s) / (s * (s + 1)) := by
    calc
      Complex.Gamma (-1 - s) = (s * (s + 1) * Complex.Gamma (-1 - s)) / (s * (s + 1)) := by
        rw [mul_comm (s * (s + 1)) (Complex.Gamma (-1 - s))]
        rw [mul_div_cancel_right₀ _ hs']
      _ = Complex.Gamma (1 - s) / (s * (s + 1)) := by
        rw [← hrel]
  -- 组装
  calc
    2 * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) * Complex.sin (↑Real.pi * (s + 2) / 2)
        = 2 * ((2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (2 : ℂ)) * Complex.Gamma (-1 - s) *
            (-Complex.sin (↑Real.pi * s / 2)) := by
            rw [hpow, hsin]
      _ = 2 * ((2 * ↑Real.pi : ℂ) ^ (s - 1) * (4 * (↑Real.pi) ^ 2)) * (Complex.Gamma (1 - s) / (s * (s + 1))) *
            (-Complex.sin (↑Real.pi * s / 2)) := by
            rw [hpow2, hG]
      _ = -4 * (↑Real.pi) ^ 2 / (s * (s + 1)) * (2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)) := by
            ring

/-- χ 的平移递推 (相位层, 模 2π):
    arg χ(s+2) - arg χ(s) = π - arg(s(s+1))。arg(-4π²) = π (模 2π)。 -/
theorem chi_arg_translation_two (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hχ : 2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) ≠ 0) :
    (((2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (s + 1) * Complex.Gamma (-1 - s) *
      Complex.sin (↑Real.pi * (s + 2) / 2)).arg : Real.Angle)
      = (((2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        + (↑Real.pi : Real.Angle)
        - ((s * (s + 1)).arg : Real.Angle) := by
  have h := chi_translation_two s hs0 hs1
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 右侧拆: -4π²/(s(s+1)) · χ(s)
  have hs' : s * (s + 1) ≠ 0 := by
    exact mul_ne_zero hs0 (by
      intro h
      apply hs1
      calc
        s = (s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h]
        _ = -1 := by norm_num)
  have hπ2 : (-4 * (↑Real.pi) ^ 2 : ℂ) ≠ 0 := by
    have hπ : (↑Real.pi : ℂ) ≠ 0 := by
      intro h
      apply Real.pi_ne_zero
      have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
      simpa using this
    exact mul_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) (pow_ne_zero 2 hπ)
  have hfac : (-4 * (↑Real.pi) ^ 2 / (s * (s + 1)) : ℂ) ≠ 0 :=
    div_ne_zero hπ2 hs'
  rw [Complex.arg_mul_coe_angle hfac hχ] at harg
  rw [Complex.arg_div_coe_angle hπ2 hs'] at harg
  -- arg(-4π²) = π (模 2π)
  have harg_neg : ((-4 * (↑Real.pi) ^ 2 : ℂ).arg : Real.Angle) = (↑Real.pi : Real.Angle) := by
    have h1 : (-4 * (↑Real.pi) ^ 2 : ℂ) = (-1 : ℂ) * (4 * (↑Real.pi) ^ 2 : ℂ) := by ring
    rw [h1]
    have hπ' : (↑Real.pi : ℂ) ≠ 0 := by
      intro h
      apply Real.pi_ne_zero
      have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
      simpa using this
    have hm := Complex.arg_mul_coe_angle (by norm_num : (-1 : ℂ) ≠ 0)
      (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 hπ'))
    rw [hm]
    rw [Complex.arg_neg_one]
    have harg4 : (4 * (↑Real.pi) ^ 2 : ℂ).arg = 0 := by
      have hc : (4 * (↑Real.pi) ^ 2 : ℂ) = (↑(4 * Real.pi ^ 2 : ℝ) : ℂ) := by norm_num
      rw [hc]
      exact Complex.arg_ofReal_of_nonneg (by positivity : 0 ≤ (4 * Real.pi ^ 2 : ℝ))
    rw [harg4]
    simp
  rw [harg_neg] at harg
  -- harg: ↑arg χ(s+2) = (π - ↑arg(s(s+1))) + ↑arg χ(s)
  -- 目标: ↑arg χ(s+2) = ↑arg χ(s) + π - ↑arg(s(s+1))
  have h1 : (↑Real.pi - ((s * (s + 1)).arg : Real.Angle))
        + ((2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
      = ((2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        + ↑Real.pi - ((s * (s + 1)).arg : Real.Angle) := by
    abel
  rw [← h1]
  exact harg



/-- 辅助: s + k = 0 ⟹ s = -k (ℂ 上, k : ℕ)。 -/
private lemma eq_neg_of_add_eq_zero (s : ℂ) (k : ℕ) (h : s + (k : ℂ) = 0) :
    s = -(k : ℂ) := by
  calc
    s = (s + (k : ℂ)) - (k : ℂ) := by ring
    _ = 0 - (k : ℂ) := by rw [h]
    _ = -(k : ℂ) := by norm_num

/-- χ 的两步平移递推 (数字层): χ(s+4) = 16π⁴/(s(s+1)(s+2)(s+3))·χ(s)。
    对称点与延拓点交换: 每一步以上一步的结果为对称点, 无固定中心。
    由 chi_translation_two 迭代两次 (χ(s+4) = χ((s+2)+2))。 -/
theorem chi_translation_four (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hs2 : s ≠ -2) (hs3 : s ≠ -3) :
    2 * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) * Complex.sin (↑Real.pi * (s + 4) / 2)
      = 16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s - 1) *
          Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2)) := by
  have h1 := chi_translation_two s hs0 hs1
  have hs1' : s + 1 ≠ 0 := by
    intro h
    apply hs1
    have h' : s + ((1 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 1 h')
  have hs2' : s + 2 ≠ 0 := by
    intro h
    apply hs2
    have h' : s + ((2 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 2 h')
  have hs3' : s + 2 ≠ -1 := by
    intro h
    apply hs3
    -- s + 2 = -1 ⟹ s = -3
    have : s = -3 := by
      have h' : s + 3 = 0 := by
        have : s + 3 = (s + 2) + 1 := by ring
        rw [this, h]
        norm_num
      simpa using (eq_neg_of_add_eq_zero s 3 h')
    exact this
  have h2 := chi_translation_two (s + 2) hs2' hs3'
  -- 归一 h2 的参数
  have hg1 : (s + 2) + 1 = s + 3 := by ring
  have hg2 : -1 - (s + 2) = -3 - s := by ring
  have hg3 : (s + 2) + 2 = s + 4 := by ring
  have hg4 : 1 - (s + 2) = -1 - s := by ring
  have hg5 : (s + 2) - 1 = s + 1 := by ring
  rw [hg1, hg2, hg3, hg4, hg5] at h2
  -- 组装
  calc
    2 * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) * Complex.sin (↑Real.pi * (s + 4) / 2)
        = -4 * (↑Real.pi) ^ 2 / ((s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s + 1) * Complex.Gamma (-1 - s) *
            Complex.sin (↑Real.pi * (s + 2) / 2)) := by
            exact h2
      _ = 16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) * (2 * (2 * ↑Real.pi) ^ (s - 1) *
            Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2)) := by
            rw [h1]
            field_simp [hs0, hs1', hs2', hs3']
            ring

/-- χ 的两步平移递推 (相位层, 模 2π): "交换延拓"的迭代 —
    arg χ(s+4) = arg χ(s) - arg(s(s+1)) - arg((s+2)(s+3))。
    arg(16π⁴) = 0 (正实数), 两步的 π 常数抵消 (π + π = 2π)。 -/
theorem chi_arg_translation_four (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ -1)
    (hs2 : s ≠ -2) (hs3 : s ≠ -3)
    (hχ : 2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) ≠ 0) :
    (((2 : ℂ) * (2 * ↑Real.pi) ^ (s + 3) * Complex.Gamma (-3 - s) *
      Complex.sin (↑Real.pi * (s + 4) / 2)).arg : Real.Angle)
      = (((2 : ℂ) * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle) := by
  have h := chi_translation_four s hs0 hs1 hs2 hs3
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 右侧拆: 16π⁴/(s(s+1)(s+2)(s+3)) · χ(s)
  have hs1' : s + 1 ≠ 0 := by
    intro h
    apply hs1
    have h' : s + ((1 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 1 h')
  have hs2' : s + 2 ≠ 0 := by
    intro h
    apply hs2
    have h' : s + ((2 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 2 h')
  have hs3' : s + 3 ≠ 0 := by
    intro h
    apply hs3
    have h' : s + ((3 : ℕ) : ℂ) = 0 := by simpa using h
    simpa using (eq_neg_of_add_eq_zero s 3 h')
  have hsden : (s * (s + 1) * (s + 2) * (s + 3)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1') hs2') hs3'
  have hπ : (↑Real.pi : ℂ) ≠ 0 := by
    intro h
    apply Real.pi_ne_zero
    have : ((↑Real.pi : ℂ).re) = (0 : ℂ).re := by rw [h]
    simpa using this
  have h16 : (16 * (↑Real.pi) ^ 4 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) (pow_ne_zero 4 hπ)
  have hfac : (16 * (↑Real.pi) ^ 4 / (s * (s + 1) * (s + 2) * (s + 3)) : ℂ) ≠ 0 :=
    div_ne_zero h16 hsden
  rw [Complex.arg_mul_coe_angle hfac hχ] at harg
  rw [Complex.arg_div_coe_angle h16 hsden] at harg
  -- arg(16π⁴) = 0 (正实数)
  have harg16 : ((16 * (↑Real.pi) ^ 4 : ℂ).arg : Real.Angle) = 0 := by
    have hc : (16 * (↑Real.pi) ^ 4 : ℂ) = (↑(16 * Real.pi ^ 4 : ℝ) : ℂ) := by norm_num
    rw [hc]
    exact congrArg (fun x : ℝ => (x : Real.Angle))
      (Complex.arg_ofReal_of_nonneg (by positivity : 0 ≤ (16 * Real.pi ^ 4 : ℝ)))
  rw [harg16] at harg
  -- harg: ↑arg χ(s+4) = 0 - ↑arg(s(s+1)) - ↑arg((s+2)(s+3)) + ↑arg χ(s)
  -- 目标: ↑arg χ(s+4) = ↑arg χ(s) - ↑arg(s(s+1)) - ↑arg((s+2)(s+3))
  have h1 : (0 : Real.Angle) - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle)
        + ((2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
      = ((2 * (2 * ↑Real.pi) ^ (s - 1) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2)).arg : Real.Angle)
        - ((s * (s + 1) * (s + 2) * (s + 3)).arg : Real.Angle) := by
    abel
  rw [← h1]
  exact harg

/-! ## 块 A: R_N / G_N 定义与初等可导性 -/

/-- R_N(s) = Σ_{n=1}^N n^{-s} + N^{1-s}/(s-1): 欧拉-麦克劳林延拓的部分和核 -/
noncomputable def zetaEmR_N (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ (Finset.range N), ((n + 1 : ℂ) ^ (-s))) + (N : ℂ) ^ (1 - s) / (s - 1)

/-- G_N(s) = (s-1)·Σ_{n=1}^N n^{-s} + N^{1-s}: (s-1)·R_N 消分母版 (在 1 处良定) -/
noncomputable def zetaEmG_N (N : ℕ) (s : ℂ) : ℂ :=
  (s - 1) * (∑ n ∈ (Finset.range N), ((n + 1 : ℂ) ^ (-s))) + (N : ℂ) ^ (1 - s)

lemma zetaEmG_N_eq_smul (N : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaEmG_N N s = (s - 1) * zetaEmR_N N s := by
  unfold zetaEmG_N zetaEmR_N
  rw [mul_add, mul_div_cancel₀ _ (sub_ne_zero.mpr hs)]

/-- R_N 在 {s | s ≠ 1} 上可导 (初等: cpow 底正实数 + 有理函数) -/
lemma zetaEmR_N_differentiableOn (N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ (zetaEmR_N N) {s : ℂ | s ≠ 1} := by
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))
  have hterm : ∀ n : ℕ, DifferentiableOn ℂ
      (fun s : ℂ => ((n + 1 : ℂ) ^ (-s))) {s : ℂ | s ≠ 1} := by
    intro n
    have hbase : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hdiff : DifferentiableOn ℂ
        (fun s : ℂ => Complex.exp (Complex.log ((n + 1 : ℂ)) * (-s))) {s : ℂ | s ≠ 1} := by
      fun_prop
    exact hdiff.congr (fun s hs => Complex.cpow_def_of_ne_zero hbase (-s))
  have hsum : DifferentiableOn ℂ
      (fun s : ℂ => (∑ n ∈ (Finset.range N), ((n + 1 : ℂ) ^ (-s)))) {s : ℂ | s ≠ 1} := by
    have hsum' : DifferentiableOn ℂ
        (∑ n ∈ (Finset.range N), (fun s : ℂ => ((n + 1 : ℂ) ^ (-s)))) {s : ℂ | s ≠ 1} := by
      exact DifferentiableOn.sum (u := Finset.range N) (A := fun n s => ((n + 1 : ℂ) ^ (-s)))
        (fun n hn => hterm n)
    exact hsum'.congr (fun s hs => by simp)
  have hnum : DifferentiableOn ℂ (fun s : ℂ => (N : ℂ) ^ (1 - s)) {s : ℂ | s ≠ 1} := by
    have hdiff : DifferentiableOn ℂ
        (fun s : ℂ => Complex.exp (Complex.log (N : ℂ) * (1 - s))) {s : ℂ | s ≠ 1} := by
      fun_prop
    exact hdiff.congr (fun s hs => Complex.cpow_def_of_ne_zero hN0 (1 - s))
  have hden : DifferentiableOn ℂ (fun s : ℂ => s - 1) {s : ℂ | s ≠ 1} := by
    fun_prop
  have hden0 : ∀ x ∈ {s : ℂ | s ≠ 1}, x - 1 ≠ 0 := by
    intro x hx
    exact sub_ne_zero.mpr hx
  exact hsum.add (hnum.div hden hden0)

/-- G_N 在带 {0 < re < 2} 上可导 (分母已消, 处处良定) -/
lemma zetaEmG_N_differentiableOn (N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ (zetaEmG_N N) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))
  have hterm : ∀ n : ℕ, DifferentiableOn ℂ
      (fun s : ℂ => ((n + 1 : ℂ) ^ (-s))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    intro n
    have hbase : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hdiff : DifferentiableOn ℂ
        (fun s : ℂ => Complex.exp (Complex.log ((n + 1 : ℂ)) * (-s))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
      fun_prop
    exact hdiff.congr (fun s hs => Complex.cpow_def_of_ne_zero hbase (-s))
  have hsum : DifferentiableOn ℂ
      (fun s : ℂ => (∑ n ∈ (Finset.range N), ((n + 1 : ℂ) ^ (-s)))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    have hsum' : DifferentiableOn ℂ
        (∑ n ∈ (Finset.range N), (fun s : ℂ => ((n + 1 : ℂ) ^ (-s)))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
      exact DifferentiableOn.sum (u := Finset.range N) (A := fun n s => ((n + 1 : ℂ) ^ (-s)))
        (fun n hn => hterm n)
    exact hsum'.congr (fun s hs => by simp)
  have hid : DifferentiableOn ℂ (fun s : ℂ => s - 1) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    fun_prop
  have hnum : DifferentiableOn ℂ (fun s : ℂ => (N : ℂ) ^ (1 - s)) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    have hdiff : DifferentiableOn ℂ
        (fun s : ℂ => Complex.exp (Complex.log (N : ℂ) * (1 - s))) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
      fun_prop
    exact hdiff.congr (fun s hs => Complex.cpow_def_of_ne_zero hN0 (1 - s))
  unfold zetaEmG_N
  exact (hid.mul hsum).add hnum

/-! ## 块 B1: 实数参数 cpow 的导数 (卷 mathlib HasDerivAt.cpow_const) -/

/-- u ↦ (u:ℂ)^s 的实数导数: s·x^{s-1} (x > 0, 卷 HasDerivAt.cpow_const) -/
lemma cpow_ofReal_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := by
  have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id (x : ℂ)) (ofReal_mem_slitPlane.2 hx)
  simpa only [mul_one] using! t.comp_ofReal

/-- u ↦ (u:ℂ)^(-s) 的实数导数 (块 B2 的一次 FTC 用) -/
lemma cpow_ofReal_neg_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x := by
  simpa using cpow_ofReal_hasDerivAt (-s) hx


/-! ## 块 B: 欧拉-麦克劳林项 term 的 ℂ 版闭式 (卷 ZetaAsymptotics 体系)

mathlib 已实现欧拉-麦克劳林第一项 (Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean):
    term n s = ∫ₙ^{n+1} (x-n)/x^{s+1} dx,  termTSum s = Σ term (n+1) s
并给出 s > 1 的恒等式 (zeta_limit_aux1):
    Σ' 1/(n+1)^s - 1/(s-1) = 1 - s·termTSum s    ⟹   ζ(s) = 1/(s-1) + 1 - s·termTSum s
右边对 0 < s 良定义 (term_welldef 只需 0 < s)。本块: 把 term 提升到 ℂ
(底正实数的 cpow), 给闭式 (分部积分) ⟹ 逐项解析; 局部一致收敛 ⟹
Weierstrass ⟹ termTSum 解析延拓到 {0 < re < 2}. 对称延拓: 恒等定理
把 s > 1 侧的恒等式唯一延拓到 (0,1) 段。 -/

/-- uIcc n (n+1) 中 x ≥ n (n ≤ n+1 已知) -/
lemma zeta_uIcc_ge {n : ℕ} {x : ℝ} (hx : x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1)) :
    (n : ℝ) ≤ x := by
  rcases (Set.mem_uIcc.mp hx) with h | h
  · exact h.1
  · exact le_trans (by simp) h.1

/-- term 的 ℂ 版: ∫ₙ^{n+1} (x-n)/x^{s+1} dx (cpow, 底正实数) -/
noncomputable def zetaTermC (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), (((x : ℂ) - (n : ℂ)) / (x : ℂ) ^ (s + 1))

/-- x ↦ (x:ℂ)^s 连续于 x > 0 (卷 ContinuousAt.cpow, 底正实数 ∈ slitPlane) -/
lemma zeta_cpow_ofReal_continuousAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun u : ℝ => (u : ℂ) ^ s) x :=
  ContinuousAt.cpow (f := fun u : ℝ => (u : ℂ)) (g := fun _ : ℝ => s)
    continuous_ofReal.continuousAt continuousAt_const (ofReal_mem_slitPlane.2 hx)

/-- FTC: ∂_x (x:ℂ)^{1-s} = (1-s)·(x:ℂ)^{-s} 于 x > 0 (卷 cpow_ofReal_hasDerivAt) -/
lemma zetaTermC_fund_integral {n : ℕ} (hn : 0 < n) {s : ℂ} (hs1 : s ≠ 1) :
    (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s)))
      = (((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)) := by
  have hd : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ (1 - s)) ((1 - s) * (x : ℂ) ^ (-s)) x := by
    intro x hx
    have hxpos : 0 < x := (Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx)
    have hd' := cpow_ofReal_hasDerivAt (1 - s) hxpos
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hd'
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := by
    exact ContinuousOn.intervalIntegrable (fun x hx =>
      (zeta_cpow_ofReal_continuousAt (-s) ((Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx))).continuousWithinAt)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hint.const_mul (1 - s))
  -- hftc : ∫ (1-s)·x^{-s} = (n+1)^{1-s} - n^{1-s} ⟹ ∫ x^{-s} = 差/(1-s)
  rw [intervalIntegral.integral_const_mul] at hftc
  calc
    (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s)))
        = ((1 - s) * (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s)))) / (1 - s) := by
            field_simp [sub_ne_zero.mpr hs1]
    _ = (((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)) := by
            rw [hftc]
            simp [Complex.ofReal_natCast, Complex.ofReal_add]

/-- term n s 的闭式 (分部积分, s ≠ 0, 1):
    term n s = ((n+1)^{1-s} - n^{1-s})/(s(1-s)) - 1/(s·(n+1)^s) -/
lemma zetaTermC_closed_form {n : ℕ} (hn : 0 < n) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    zetaTermC n s = (((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (s * (1 - s)))
        - 1 / (s * (n + 1 : ℂ) ^ s) := by
  -- 被积代数: (x-n)/x^{s+1} = x^{-s} - n·x^{-s-1} (x > 0)
  have hf : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
      (((x : ℂ) - (n : ℂ)) / (x : ℂ) ^ (s + 1))
        = ((x : ℂ) ^ (-s)) - (n : ℂ) * ((x : ℂ) ^ (-s - 1)) := by
    intro x hx
    have hxpos : 0 < x := (Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx)
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hxpos)
    have hx1 : (x : ℂ) ^ (1 : ℂ) = (x : ℂ) := by simp
    have hxpow : (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
      nth_rewrite 1 [← hx1]
      rw [← Complex.cpow_add 1 (-(s + 1)) hx0]
      congr 1
      ring
    calc
      ((x : ℂ) - (n : ℂ)) / (x : ℂ) ^ (s + 1)
          = (x : ℂ) / (x : ℂ) ^ (s + 1) - (n : ℂ) / (x : ℂ) ^ (s + 1) := by rw [sub_div]
      _ = (x : ℂ) * (x : ℂ) ^ (-(s + 1)) - (n : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
            congr 2
            · rw [div_eq_mul_inv, ← Complex.cpow_neg]
            · rw [div_eq_mul_inv, ← Complex.cpow_neg]
      _ = (x : ℂ) ^ (-s) - (n : ℂ) * (x : ℂ) ^ (-s - 1) := by
            rw [hxpow]
            congr 1
            rw [show (-(s + 1) : ℂ) = -s - 1 by ring]
  -- ∫ x^{-s} 与 ∫ x^{-s-1} 的 FTC
  have hint2 : (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s - 1)))
      = (((n + 1 : ℂ) ^ (-s) - (n : ℂ) ^ (-s)) / (-s)) := by
    have hd2 : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
        HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x := by
      intro x hx
      have hxpos : 0 < x := (Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx)
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        cpow_ofReal_hasDerivAt (-s) hxpos
    have hint' : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) MeasureTheory.volume
        (n : ℝ) ((n : ℝ) + 1) := by
      exact ContinuousOn.intervalIntegrable (fun x hx =>
        (zeta_cpow_ofReal_continuousAt (-s - 1) ((Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx))).continuousWithinAt)
    have hftc2 := intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 (hint'.const_mul (-s))
    rw [intervalIntegral.integral_const_mul] at hftc2
    calc
      (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s - 1)))
          = ((-s) * (∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s - 1)))) / (-s) := by
              field_simp [hs0]
      _ = (((n + 1 : ℂ) ^ (-s) - (n : ℂ) ^ (-s)) / (-s)) := by
            rw [hftc2]
            simp [Complex.ofReal_natCast, Complex.ofReal_add]
  -- 组装: ∫(x^{-s} - n·x^{-s-1}) = ∫x^{-s} - n·∫x^{-s-1}
  have hint3 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := by
    exact ContinuousOn.intervalIntegrable (fun x hx =>
      (zeta_cpow_ofReal_continuousAt (-s) ((Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx))).continuousWithinAt)
  have hint4 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := by
    exact ContinuousOn.intervalIntegrable (fun x hx =>
      (zeta_cpow_ofReal_continuousAt (-s - 1) ((Nat.cast_pos.mpr hn).trans_le (zeta_uIcc_ge hx))).continuousWithinAt)
  rw [zetaTermC, intervalIntegral.integral_congr hf]
  rw [intervalIntegral.integral_sub hint3 (hint4.const_mul (n : ℂ))]
  rw [intervalIntegral.integral_const_mul (n : ℂ)]
  rw [zetaTermC_fund_integral hn hs1, hint2]
  -- 目标: A/(1-s) - n·(C-D)/(-s) = A/(s(1-s)) - 1/(sE)  (A=(n+1)^{1-s}-n^{1-s}, ...)
  -- cpow 合并引理
  have hnp1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hnn : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hmerge1 : ((n + 1 : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s) = (n + 1 : ℂ) := by
    rw [← Complex.cpow_add (1 - s) s hnp1]
    have : (1 - s) + s = 1 := by ring
    rw [this]
    simp
  have hmerge2 : ((n + 1 : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s) = 1 := by
    rw [← Complex.cpow_add (-s) s hnp1]
    have : (-s) + s = 0 := by ring
    rw [this]
    simp
  have hmerge3 : (n : ℂ) * ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (1 - s) := by
    nth_rewrite 1 [← Complex.cpow_one (n : ℂ)]
    rw [← Complex.cpow_add 1 (-s) hnn]
    congr 1
  -- 通分到 s(1-s), calc 链化简 (每步 ring + 单 rw, 控制 cpow 乘积形态)
  field_simp [hs0, sub_ne_zero.mpr hs1]
  calc
    (s * (((n + 1 : ℂ) ^ (1 - s)) - ((n : ℂ) ^ (1 - s)))
        - -(n * (1 - s) * (((n + 1 : ℂ) ^ (-s)) - ((n : ℂ) ^ (-s))))) * ((n + 1 : ℂ) ^ s)
        = s * ((((n + 1 : ℂ) ^ (1 - s)) - ((n : ℂ) ^ (1 - s))) * ((n + 1 : ℂ) ^ s))
            + n * (1 - s) * ((((n + 1 : ℂ) ^ (-s)) - ((n : ℂ) ^ (-s))) * ((n + 1 : ℂ) ^ s)) := by
            ring
    _ = s * ((((n + 1 : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s))
            - (((n : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s)))
            + n * (1 - s) * ((((n + 1 : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s))
            - (((n : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s))) := by
            ring
    _ = s * (((n + 1 : ℂ)) - (((n : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s)))
            + n * (1 - s) * (1 - (((n : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s))) := by
            rw [hmerge1, hmerge2]
    _ = s * (n + 1 : ℂ) + n * (1 - s) - (n : ℂ) * ((n : ℂ) ^ (-s)) * ((n + 1 : ℂ) ^ s) := by
            conv_lhs => rw [← hmerge3]
            ring
    _ = ((n + 1 : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) * ((n + 1 : ℂ) ^ s) - (1 - s) := by
            rw [hmerge3]
            rw [sub_mul, hmerge1]
            ring



/-- 临界线参数化: z(t) = 1/2 + t·i。 -/
def zetaLine (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- u(t) = ζ(1/2+it)/|ζ(1/2+it)|: ζ 沿临界线的单位化 (相位)。 -/
def zetaUnitOnLine (t : ℝ) : ℂ :=
  riemannZeta (zetaLine t) / ‖riemannZeta (zetaLine t)‖

/-- **S(T) = (1/π)·arg u(T) (主枝)**: 翻转序列的相位归一。
    e^{iπ} 桥接的指数: e^{iπS(T)} = u(T)。 -/
def Sfunc (T : ℝ) : ℝ :=
  (Complex.log (zetaUnitOnLine T)).im / Real.pi

/-- u 的模恒 1: ‖ζ/|ζ|‖ = 1 (ζ ≠ 0 处)。 -/
theorem zetaUnitOnLine_norm_one (T : ℝ) (hz : riemannZeta (zetaLine T) ≠ 0) :
    ‖zetaUnitOnLine T‖ = 1 := by
  unfold zetaUnitOnLine
  rw [norm_div]
  -- ‖(‖ζ‖ : ℂ)‖ = |‖ζ‖| = ‖ζ‖ (非负)
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (norm_nonneg _)]
  -- ‖ζ‖/‖ζ‖ = 1 (ℝ)
  exact div_self (norm_ne_zero_iff.mpr hz)

/-- **e^{iπ} 桥接定理**: e^{i·π·S(T)} = u(T) —
    S(T) 的 e^{iπ} 次幂 = 翻转单位元 (相位)。 -/
theorem exp_pi_i_S_eq_u (T : ℝ) (hz : riemannZeta (zetaLine T) ≠ 0) :
    Complex.exp (((I : ℂ) * (Real.pi : ℂ)) * (Sfunc T : ℂ)) = zetaUnitOnLine T := by
  -- u ≠ 0 (ζ ≠ 0)
  have hu : zetaUnitOnLine T ≠ 0 := by
    unfold zetaUnitOnLine
    exact div_ne_zero hz (by exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))
  -- |u| = 1 ⟹ log u 纯虚: 实部 log|u| = log 1 = 0
  have hlog_re : (Complex.log (zetaUnitOnLine T)).re = 0 := by
    rw [Complex.log_re, zetaUnitOnLine_norm_one T hz]
    simp
  -- log u = i·Im log u (纯虚 ⟹ 虚轴表示)
  have hlog : Complex.log (zetaUnitOnLine T) = I * ((Complex.log (zetaUnitOnLine T)).im : ℂ) := by
    apply Complex.ext
    · simp [hlog_re]
    · simp
  -- 代数: i·π·S = i·π·(Im log u/π) = i·Im log u = log u
  have harg : ((I : ℂ) * (Real.pi : ℂ)) * (Sfunc T : ℂ) = Complex.log (zetaUnitOnLine T) := by
    unfold Sfunc
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    -- ↑(im/π) = ↑im/↑π, 消 π: i·π·(im/π) = i·im
    rw [Complex.ofReal_div]
    field_simp [hp]
    rw [← hlog]
  -- e^{log u} = u
  rw [harg]
  exact Complex.exp_log hu

-- 翻转的 e^{iπ} 表示 (声明): u 跨零点翻转 (u⁻ = -u⁺) ⟺ e^{iπS} 跳变 π:
--   e^{iπ·S(t₀⁻)} = -e^{iπ·S(t₀⁺)} (由 exp_pi_i_S_eq_u + 翻转比值 C032)。
-- 符号改变 = e^{iπ} 因子 (π = 发散↔周期转换); 具体拼装见矩形闭合。
-- (翻转比值 C032 已机证: u(σt)/u(t) → (-1)^m = e^{iπm}; 本文件给 e^{iπ} 形式)


/-- **u 的共轭对称**: u(-T) = conj u(T) — ζ 实系数 (riemannZeta_conj)
    ⟹ 相位方向反号 (虚部方向对消)。 -/
theorem zetaUnitOnLine_conj (T : ℝ) : zetaUnitOnLine (-T) = conj (zetaUnitOnLine T) := by
  unfold zetaUnitOnLine
  -- ζ(z(-T)) = conj ζ(z(T)): z(-T) = conj z(T) + riemannZeta_conj
  have hline : zetaLine (-T) = conj (zetaLine T) := by
    unfold zetaLine
    apply Complex.ext
    · simp
    · simp
  have hz : riemannZeta (zetaLine (-T)) = conj (riemannZeta (zetaLine T)) := by
    rw [hline, riemannZeta_conj]
  rw [hz]
  -- conj 保持除法与 norm (|ζ| 实数)
  rw [map_div₀, conj_ofReal, norm_conj]


/-- **S(T) 的奇性 (共轭对称)**: S(-T) = -S(T) (arg u(T) ≠ π 时)。
    u(-T) = conj u(T) (实系数 ζ) + arg(conj z) = -arg z (arg_conj,
    π 边界由条件排除) ⟹ 相位方向反号 (虚部方向对消)。 -/
theorem Sfunc_neg (T : ℝ) (_hz : riemannZeta (zetaLine T) ≠ 0)
    (hnot : (Complex.log (zetaUnitOnLine T)).im ≠ Real.pi) :
    Sfunc (-T) = -Sfunc T := by
  have hnot' : (zetaUnitOnLine T).arg ≠ Real.pi := by
    simpa [Complex.log_im] using hnot
  calc
    Sfunc (-T) = (zetaUnitOnLine (-T)).arg / Real.pi := by
      unfold Sfunc
      rw [Complex.log_im]
    _ = (conj (zetaUnitOnLine T)).arg / Real.pi := by rw [zetaUnitOnLine_conj]
    _ = -(zetaUnitOnLine T).arg / Real.pi := by
      rw [arg_conj, if_neg hnot']
    _ = -((Complex.log (zetaUnitOnLine T)).im / Real.pi) := by
      rw [Complex.log_im]
      ring
    _ = -Sfunc T := by
      unfold Sfunc
      rfl


/-- **S 的主枝界**: |S(T)| ≤ 1 — arg 主枝 ∈ (-π, π], S = arg/π ∈ (-1, 1]。
    e^{iπS} = u 的指数有界 (u 在单位圆上, 幅角主枝有界)。 -/
theorem Sfunc_abs_le_one (T : ℝ) : |Sfunc T| ≤ 1 := by
  unfold Sfunc
  -- |arg u/π| ≤ 1: |arg u| ≤ π
  have harg : |(Complex.log (zetaUnitOnLine T)).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact abs_arg_le_pi (zetaUnitOnLine T)
  -- |arg/π| ≤ 1 ⟸ |arg| ≤ π
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [abs_div, abs_of_pos hπ]
  -- |arg|/π ≤ 1 ⟸ |arg| ≤ π
  rw [div_le_one hπ]
  exact harg


  -- ============================================================
  -- T6l: 增长控制落点 — |S(T)| ≤ 1 ⟹ S(T) = O(log T) (2026-08-19)
  -- e^{iπ} 桥的界: S(T) = (1/π)·Im log u(T) 是主枝相位归一,
  -- |arg| ≤ π ⟹ |S| ≤ 1 (逐点有界), 平凡蕴含渐近界 O(log T)。
  -- Backlund 的完整 S(T) = O(log T) (部分和误差 polyError 控制)
  -- 是经典 KNOWN (标注引用); 本定理给出桥接落点。
  -- ============================================================

/-- **增长控制落点**: |S(T)| ≤ 1 ≤ log T (T ≥ e) — S(T) = O(log T) 的
    逐点版本。e^{iπS} = u 桥的界: 主枝 arg 有界 ⟹ S 有界。 -/
theorem Sfunc_le_log (T : ℝ) (hT : Real.exp 1 ≤ T) :
    |Sfunc T| ≤ Real.log T := by
  have hlog : (1 : ℝ) ≤ Real.log T := by
    have hloge : Real.log (Real.exp 1) = 1 := by simp [Real.log_exp]
    rw [← hloge]
    exact Real.log_le_log (Real.exp_pos 1) hT
  exact le_trans (Sfunc_abs_le_one T) hlog


/-- 多项式级数 ∑ k^{-s} (k > n) 的截断误差模型: e(n) = n^{1-s}/(s-1)。
    来源: ∫_n^∞ x^{-s} dx = n^{1-s}/(s-1) (积分判别, s > 1)。 -/
def polyError (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 - s) / (s - 1)

/-- **核心比率定理**: e(2n)/e(n) = 2^{1-s} — 每层误差比率恒定,
    测量一次 e(n₀) ⟹ 推出所有 e(2^k·n₀)。 -/
theorem poly_error_ratio {s : ℝ} (hs : s ≠ 1) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) / polyError s n = (2 : ℝ) ^ (1 - s) := by
  dsimp [polyError]
  have hpow : ((2 * n : ℕ) : ℝ) ^ (1 - s) = (2 : ℝ) ^ (1 - s) * (n : ℝ) ^ (1 - s) := by
    rw [show ((2 * n : ℕ) : ℝ) = (2 : ℝ) * (n : ℝ) by norm_num]
    rw [Real.mul_rpow]
    · norm_num
    · exact_mod_cast (Nat.zero_le n)
  rw [hpow]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnsq : (n : ℝ) ^ (1 - s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos (1 - s))
  field_simp [hs, hnsq]

/-- 误差序列预测: 测量一次推全部 — e(2n) = e(n)·2^{1-s}。 -/
theorem error_seq_predicts {s : ℝ} (hs : s ≠ 1) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := by
  have hr := poly_error_ratio hs hn
  dsimp [polyError] at hr ⊢
  -- 从比率定理: e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
  -- 需要 e(n) ≠ 0
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnsq : (n : ℝ) ^ (1 - s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos (1 - s))
  have hne : polyError s n ≠ 0 := by
    dsimp [polyError]
    exact div_ne_zero hnsq (sub_ne_zero.mpr hs)
  -- hr : e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
  have hr' : polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := by
    -- 从比率: e(2n)/e(n) = 2^{1-s} ⟹ e(2n) = e(n)·2^{1-s}
    dsimp [polyError] at hr ⊢
    -- 同 poly_error_ratio 的代数
    have hpow : ((2 * n : ℕ) : ℝ) ^ (1 - s) = (2 : ℝ) ^ (1 - s) * (n : ℝ) ^ (1 - s) := by
      rw [show ((2 * n : ℕ) : ℝ) = (2 : ℝ) * (n : ℝ) by norm_num]
      rw [Real.mul_rpow]
      · norm_num
      · exact_mod_cast (Nat.zero_le n)
    rw [hpow] at hr ⊢
    -- hr : (2^{1-s}·n^{1-s}/(s-1)) / (n^{1-s}/(s-1)) = 2^{1-s}
    -- 目标: (2^{1-s}·n^{1-s})/(s-1) = (n^{1-s}/(s-1))·2^{1-s}
    field_simp [hs, hnsq]
  exact hr' 

/-- 误差单调递减: n 加倍 ⟹ 误差按 2^{1-s} 收缩 (s > 1 时 2^{1-s} < 1)。 -/
theorem poly_error_monotone {s : ℝ} (hs1 : 1 < s) {n : ℕ} (hn : 0 < n) :
    polyError s (2 * n) < polyError s n := by
  change ((2 * n : ℕ) : ℝ) ^ (1 - s) / (s - 1) < (n : ℝ) ^ (1 - s) / (s - 1)
  have hr := error_seq_predicts (ne_of_gt hs1) hn
  -- e(2n) = e(n)·2^{1-s}, s > 1 ⟹ 2^{1-s} < 1, e(n) > 0
  have hpos : 0 < polyError s n := by
    dsimp [polyError]
    -- n^{1-s} > 0 (n > 0), s-1 > 0
    exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) (1 - s)) (sub_pos.mpr hs1)
  have hratio : (2 : ℝ) ^ (1 - s) < 1 := by
    -- s > 1 ⟹ 1-s < 0 ⟹ 2^{1-s} < 1 (rpow_lt_one_iff)
    have hneg : 1 - s < 0 := by linarith
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Or.inl ⟨by norm_num, hneg⟩
  calc
    polyError s (2 * n) = polyError s n * (2 : ℝ) ^ (1 - s) := hr
    _ < polyError s n * 1 := by
      exact mul_lt_mul_of_pos_left hratio hpos
    _ = polyError s n := by ring

/-- 提前量反解: 要精度 ε ⟹ n ≥ (1/ε)^{1/(s-1)} 时 e(n) ≤ ε/(s-1)。
    从 e(n) = n^{1-s}/(s-1) 反解 (s > 1): n^{1-s} ≤ ε ⟺ n ≥ (1/ε)^{1/(s-1)}。 -/
theorem error_precision_bound {s : ℝ} (hs1 : 1 < s) {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hn : (1 / ε) ^ (1 / (s - 1)) ≤ (n : ℝ)) :
    polyError s n ≤ ε / (s - 1) := by
  dsimp [polyError]
  have hs1' : 0 < s - 1 := sub_pos.mpr hs1
  have hεinv : 0 < 1 / ε := one_div_pos.mpr hε
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hεinv (1 / (s - 1))) hn
  -- (1/ε)^{1/(s-1)} ≤ n ⟹ 1/ε ≤ n^{s-1} (rpow (s-1) 保序 + 复合)
  have hle : 1 / ε ≤ (n : ℝ) ^ (s - 1) := by
    have h1 : ((1 / ε) ^ (1 / (s - 1))) ^ (s - 1) ≤ (n : ℝ) ^ (s - 1) :=
      Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hεinv (1 / (s - 1)))) hn (le_of_lt hs1')
    have hcomp : ((1 / ε) ^ (1 / (s - 1))) ^ (s - 1) = 1 / ε := by
      rw [← Real.rpow_mul (le_of_lt hεinv) (1 / (s - 1)) (s - 1)]
      congr 1
      field_simp [hs1', hε]
      simp [pow_one]
      field_simp [hε]
    rwa [hcomp] at h1
  -- 1/ε ≤ n^{s-1} ⟹ n^{1-s} = 1/n^{s-1} ≤ ε (倒数保序)
  have hle2 : (n : ℝ) ^ (1 - s) ≤ ε := by
    have hneg : (n : ℝ) ^ (1 - s) = (n : ℝ) ^ (-(s - 1) : ℝ) := by
      congr 1
      ring
    rw [hneg]
    rw [Real.rpow_neg (le_of_lt hnpos) (s - 1)]
    -- 目标: (n^{s-1})⁻¹ ≤ ε ⟸ hle: 1/ε ≤ n^{s-1}
    have hle' : (n : ℝ) ^ (s - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
    rw [inv_eq_one_div]
    have hle'' : 1 / (n : ℝ) ^ (s - 1) ≤ 1 / (1 / ε) := by
      exact one_div_le_one_div_of_le hεinv hle
    -- 1/(1/ε) = ε
    have hle3 : 1 / (n : ℝ) ^ (s - 1) ≤ ε := by
      simpa using hle''
    exact hle3
  -- n^{1-s} ≤ ε ⟹ n^{1-s}/(s-1) ≤ ε/(s-1)
  exact div_le_div_of_nonneg_right hle2 (le_of_lt hs1')


/-- 零点判定: ζ(z) = 0 ⟺ Re ζ(z) = 0 ∧ Im ζ(z) = 0 (副本: proof.lean 同定理). -/
theorem zeta_eq_zero_iff_re_im (z : ℂ) :
    riemannZeta z = 0 ↔ (riemannZeta z).re = 0 ∧ (riemannZeta z).im = 0 := by
  constructor
  · intro h
    constructor <;> simp [h]
  · intro h
    apply Complex.ext
    · exact h.1
    · exact h.2

/-- 零点在分裂锥面上: ζ(z) = 0 ⟹ normSq(ζ(z)) = Re²-Im² = 0. -/
theorem zero_split_normSq (z : ℂ) (hz : riemannZeta z = 0) :
    (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 = 0 := by
  have hri := (zeta_eq_zero_iff_re_im z).mp hz
  rw [hri.1, hri.2]
  norm_num

/-- 零点避开两个正交欧拉圆: normSq(ζ(z)) = 0 ≠ ±1
    (半径 1 圆 normSq=1 与半径 i 圆 normSq=-1 均不含零点). -/
theorem zero_not_on_euler_circles (z : ℂ) (hz : riemannZeta z = 0) :
    (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 ≠ 1 ∧
      (riemannZeta z).re ^ 2 - (riemannZeta z).im ^ 2 ≠ -1 := by
  have h0 := zero_split_normSq z hz
  constructor <;> linarith


/-- ζ 的零点集 = mathlib 的 `riemannZetaZeros`。 -/
def zetaZeroSet : Set ℂ := riemannZetaZeros

/-- 零点集闭。 -/
lemma isClosed_zetaZeroSet : IsClosed zetaZeroSet := by
  simpa [zetaZeroSet] using isClosed_riemannZetaZeros

/-- 零点集离散: 每个零点孤立。 -/
lemma isDiscrete_zetaZeroSet : IsDiscrete zetaZeroSet := by
  simpa [zetaZeroSet] using isDiscrete_riemannZetaZeros

/-- 紧致集 ∩ 零点集有限。 -/
lemma IsCompact.inter_zetaZeroSet_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ zetaZeroSet).Finite := by
  simpa [zetaZeroSet] using hS.inter_riemannZetaZeros_finite

/-- 带内零点有限: [0,1]×[-T,T] 内仅有限多个零点。
带是紧致的 (含于闭球 ‖z‖ ≤ sqrt(1+T²)+1, 离散零点在紧集内有限)。 -/
theorem zeta_zeros_finite_in_strip (T : ℝ) :
    ({z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}).Finite := by
  let R : ℝ := Real.sqrt (1 + T ^ 2) + 1
  have hsub : {z : ℂ | riemannZeta z = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
      ⊆ Metric.closedBall (0 : ℂ) R ∩ zetaZeroSet := by
    intro z hz
    rcases hz with ⟨hz0, hre0, hre1, him⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hnormSq : Complex.normSq z ≤ 1 + T ^ 2 := by
        rw [Complex.normSq_apply]
        have h1 : z.re ^ 2 ≤ 1 := by
          have hmul : z.re * z.re ≤ 1 * 1 := mul_le_mul hre1 hre1 hre0 zero_le_one
          simpa [pow_two] using hmul
        have h2 : z.im ^ 2 ≤ T ^ 2 := by
          have hT : 0 ≤ T := le_trans (abs_nonneg z.im) him
          have hmul : |z.im| * |z.im| ≤ T * T := mul_le_mul him him (abs_nonneg z.im) hT
          have h2' : |z.im| ^ 2 ≤ T ^ 2 := by simpa [pow_two] using hmul
          nlinarith [h2', sq_abs (z.im)]
        nlinarith
      calc
        ‖z‖ = Real.sqrt (‖z‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]
        _ = Real.sqrt (Complex.normSq z) := by rw [Complex.normSq_eq_norm_sq]
        _ ≤ Real.sqrt (1 + T ^ 2) := Real.sqrt_le_sqrt hnormSq
        _ ≤ R := by
          dsimp [R]
          linarith
    · simpa [zetaZeroSet, mem_riemannZetaZeros] using hz0
  have hfin : (Metric.closedBall (0 : ℂ) R ∩ zetaZeroSet).Finite :=
    IsCompact.inter_zetaZeroSet_finite (isCompact_closedBall (x := (0 : ℂ)) R)
  exact hfin.subset hsub


/-- 倍增乘子的显式相位: 2^(1/2-it) = √2·(cos(t·ln2) - i·sin(t·ln2)),
    相位 = -t·ln2 (线性) — Legendre 倍增公式 2^{1-2s} 在 s = 1/4+it/2 的乘子。 -/
theorem cpow_two_half_minus_im (t : ℝ) :
    (2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ)
      = (Real.exp (Real.log 2 / 2) : ℂ) * (Real.cos (t * Real.log 2) : ℂ)
        - (Real.exp (Real.log 2 / 2) : ℂ) * (Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  have hdecomp : (Real.log 2 : ℂ) * ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)
      = ((Real.log 2 / 2 : ℝ) : ℂ) + ((-(t * Real.log 2) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.exp_mul_I]
  simp
  ring


/-- A: 共轭相位 (模 2π): arg Γ(conj s) = -arg Γ(s)。
    无条件: arg_conj_coe_angle 是 Angle 层恒等式, 分支在模 2π 下消失。 -/
theorem gamma_conj_arg_angle (s : ℂ) :
    ((Complex.Gamma ((starRingEnd ℂ) s)).arg : Real.Angle)
      = -((Complex.Gamma s).arg : Real.Angle) := by
  rw [Complex.Gamma_conj]
  exact Complex.arg_conj_coe_angle (Complex.Gamma s)

/-- B: 倍增相位 (模 2π, s = 1/4+it/2): Legendre 倍增公式的 arg 版本。
    arg Γ(1/4+) + arg Γ(3/4+) = arg Γ(1/2+) + (log 2^{1/2-it}).im。 -/
theorem gamma_doubling_arg_angle (t : ℝ) :
    ((Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
        + ((Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
      = ((Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg : Real.Angle)
        + ((Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im : Real.Angle) := by
  let s : ℂ := (1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  have hs_pos : 0 < s.re := by dsimp [s]; simp
  have hs2_pos : 0 < (s + 1 / 2).re := by dsimp [s]; simp; norm_num
  have h2s_pos : 0 < (2 * s).re := by dsimp [s]; simp
  have hs_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs_pos
  have hs2_ne : Complex.Gamma (s + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2_pos
  have h2s_ne : Complex.Gamma (2 * s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h2s_pos
  have hpow_ne : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have hsqrt_ne : (↑(Real.sqrt Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  -- Legendre 倍增公式 (无条件)
  have h := Complex.Gamma_mul_Gamma_add_half s
  -- 取 arg 进 Real.Angle
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) h
  -- 左侧: Γ(s)·Γ(s+1/2)
  rw [Complex.arg_mul_coe_angle hs_ne hs2_ne] at harg
  -- 右侧: (Γ(2s)·2^{1-2s})·√π
  rw [Complex.arg_mul_coe_angle (mul_ne_zero h2s_ne hpow_ne) hsqrt_ne] at harg
  rw [Complex.arg_mul_coe_angle h2s_ne hpow_ne] at harg
  -- arg √π = 0
  have harg_sqrt : (↑(Real.sqrt Real.pi) : ℂ).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg _)
  simp [harg_sqrt] at harg
  -- arg(2^{1-2s}) = (log 2^{1-2s}).im (log_im 反向)
  have hlog : (Complex.log ((2 : ℂ) ^ (1 - 2 * s))).im = ((2 : ℂ) ^ (1 - 2 * s)).arg := by
    rw [Complex.log_im]
  rw [← hlog] at harg
  -- 替换 s 的具体值: s+1/2 = 3/4+it/2, 2s = 1/2+it, 1-2s = 1/2-it
  have hs12 : s + (2 : ℂ)⁻¹ = (3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2 := by
    dsimp [s]; ring
  have h2s : 2 * s = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
    dsimp [s]; ring
  have h12s : 1 - 2 * s = ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ) := by
    dsimp [s]; ring
  -- h12s 需在 h2s 前: h2s 会先替换掉 harg 中的 2*s
  rw [hs12, h12s, h2s] at harg
  dsimp [s] at harg
  exact harg

/-- C: 反射相位 (模 2π, z = 3/4+it/2):
    arg Γ(3/4+) + arg Γ(1/4-) = -(log sin(π(3/4+it/2))).im。
    Euler 反射公式 Γ(z)Γ(1-z) = π/sin(πz) 的 arg 版本; sin 非零由左侧
    Γ 非零 (re > 0) 自动推出, 无整数/无理数论证。 -/
theorem gamma_reflection_arg_angle (t : ℝ) :
    ((Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
        + ((Complex.Gamma ((1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2)).arg : Real.Angle)
      = -((Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im : Real.Angle) := by
  let z : ℂ := (3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  have hz_pos : 0 < z.re := by dsimp [z]; simp
  have h1z_pos : 0 < (1 - z).re := by dsimp [z]; simp; norm_num
  have hz_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz_pos
  have h1z_ne : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1z_pos
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  -- sin(πz) ≠ 0: 由 Γ(z)Γ(1-z) = π/sin(πz) ≠ 0 推出
  have hleft_ne : Complex.Gamma z * Complex.Gamma (1 - z) ≠ 0 := mul_ne_zero hz_ne h1z_ne
  have hsin_ne : Complex.sin (↑Real.pi * z) ≠ 0 := by
    intro hs
    have hzero : Complex.Gamma z * Complex.Gamma (1 - z) = 0 := by
      rw [hrefl, hs]
      simp
    exact hleft_ne hzero
  -- 取 arg 进 Real.Angle
  have harg := congrArg (fun x : ℂ => (x.arg : Real.Angle)) hrefl
  -- 左侧: Γ(z)·Γ(1-z)
  rw [Complex.arg_mul_coe_angle hz_ne h1z_ne] at harg
  -- 右侧: arg(π/sin(πz)) = arg π - arg sin(πz)
  rw [Complex.arg_div_coe_angle (by exact_mod_cast Real.pi_ne_zero) hsin_ne] at harg
  -- arg π = 0
  have harg_pi : (↑Real.pi : ℂ).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)
  rw [harg_pi] at harg
  simp at harg
  -- arg(sin(πz)) = (log sin(πz)).im (log_im 反向)
  have hlog : (Complex.log (Complex.sin (↑Real.pi * z))).im =
      (Complex.sin (↑Real.pi * z)).arg := by
    rw [Complex.log_im]
  rw [← hlog] at harg
  -- 替换 z 的具体值: 1-z = 1/4-it/2
  have h1z : 1 - z = (1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2 := by
    dsimp [z]; ring
  rw [h1z] at harg
  dsimp [z] at harg
  exact harg

/-- D: 组合 (模 2π): 2·arg Γ(1/4+it/2) = arg Γ(1/2+it) + (log 2^{1/2-it}).im
    + (log sin(π(3/4+it/2))).im。
    代数: B + C + A ⟹ 2a = d + e + f (Γ 完全消去)。 -/
theorem gamma_quarter_phase_combine (t : ℝ) :
    (((2 : ℝ) * (Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg) : Real.Angle)
      = ((Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg : Real.Angle)
        + ((Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im : Real.Angle)
        + ((Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im : Real.Angle) := by
  let s : ℂ := (1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2
  let a : ℝ := (Complex.Gamma s).arg
  let b : ℝ := (Complex.Gamma ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).arg
  let d : ℝ := (Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).arg
  let e : ℝ := (Complex.log ((2 : ℂ) ^ ((1 / 2 : ℂ) - (t : ℂ) * Complex.I : ℂ))).im
  let f : ℝ := (Complex.log (Complex.sin (↑Real.pi * ((3 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)))).im
  have hA := gamma_conj_arg_angle s
  have hB := gamma_doubling_arg_angle t
  have hC := gamma_reflection_arg_angle t
  -- hA 里 conj s = 1/4-it/2, 用于消 hC 中的 Γ(1/4-)
  have hconj : (starRingEnd ℂ) s = (1 / 4 : ℂ) - (t : ℂ) * Complex.I / 2 := by
    apply Complex.ext <;> dsimp [s] <;> simp
  rw [hconj] at hA
  -- hA: ↑arg Γ(1/4-) = -↑arg Γ(s) = -↑a
  rw [hA] at hC
  -- hC: ↑b + (-↑a) = -↑f ⟹ ↑b = ↑a - ↑f
  have hb : (↑b : Real.Angle) = (↑a : Real.Angle) - (↑f : Real.Angle) := by
    calc
      (↑b : Real.Angle) = (↑b + (-↑a)) + ↑a := by abel
      _ = (-↑f) + (↑a : Real.Angle) := by rw [hC]
      _ = (↑a : Real.Angle) - (↑f : Real.Angle) := by abel
  -- hB: ↑a + ↑b = ↑d + ↑e
  rw [hb] at hB
  -- ↑a + (↑a - ↑f) = ↑d + ↑e ⟹ ↑a + ↑a = ↑d + ↑e + ↑f
  have hsum : (↑a : Real.Angle) + (↑a : Real.Angle)
      = (↑d : Real.Angle) + (↑e : Real.Angle) + (↑f : Real.Angle) := by
    calc
      (↑a : Real.Angle) + (↑a : Real.Angle) = (↑a + (↑a - ↑f)) + (↑f : Real.Angle) := by abel
      _ = (↑d + ↑e) + (↑f : Real.Angle) := by rw [hB]
      _ = (↑d : Real.Angle) + (↑e : Real.Angle) + (↑f : Real.Angle) := by abel
  -- 目标左侧: ↑(2·a) = ↑a + ↑a
  have htwo : (↑(2 * a) : Real.Angle) = (↑a : Real.Angle) + (↑a : Real.Angle) := by
    rw [two_mul]; simp
  rw [htwo]
  dsimp [a, d, e, f]
  exact hsum


/-- sin(π/2 + iπt) = cosh(πt) 实正 (sin 的显式相位在 π/2 处退化为双曲余弦)。 -/
theorem sin_pi_half_add_mul_I (t : ℝ) :
    Complex.sin (↑Real.pi / 2 + (t : ℂ) * ↑Real.pi * Complex.I)
      = (Real.cosh (Real.pi * t) : ℂ) := by
  have h := Complex.sin_add_mul_I (↑Real.pi / 2) ((Real.pi * t : ℝ) : ℂ)
  -- h: sin(↑(π/2) + ↑(π·t)·I) = sin(↑(π/2))·cosh(↑(π·t)) + cos(↑(π/2))·sinh(↑(π·t))·I
  -- 匹配 LHS: (t:ℂ)·(↑π:ℂ) = ↑(π·t)(ofReal_mul)
  have hL : ↑Real.pi / 2 + (t : ℂ) * ↑Real.pi * Complex.I
      = ↑(Real.pi / 2) + ↑(Real.pi * t) * Complex.I := by
    norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add]
    ring
  rw [hL]
  -- sin(π/2) = 1, cos(π/2) = 0:simp 化简
  simpa using h

/-- Γ 在临界线上的模 (对称操作的产物): |Γ(1/2+it)|² = π/cosh(πt) 精确。
    反射对称 (Γ(s)Γ(1-s) = π/sin(πs)) + 共轭 (Γ(conj s) = conj Γ(s))
    + sin 显式 (sin(π/2+iπt) = cosh(πt)) — Stirling 的模部分被对称性替代。 -/
theorem gamma_abs_sq_on_line (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = Real.pi / Real.cosh (Real.pi * t) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hconj : 1 - s = (starRingEnd ℂ) s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
  -- 反射: Γ(s)·Γ(1-s) = π/sin(πs)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  -- 1-s = conj s, Γ(conj s) = conj Γ(s)
  rw [hconj] at hrefl
  rw [Complex.Gamma_conj] at hrefl
  -- sin(πs) = cosh(πt) (π·s = π/2 + iπt)
  have harg : ↑Real.pi * s = ↑Real.pi / 2 + (t : ℂ) * ↑Real.pi * Complex.I := by
    dsimp [s]
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [harg] at hrefl
  rw [sin_pi_half_add_mul_I] at hrefl
  -- Γ(s)·conj Γ(s) = ↑‖Γ(s)‖² (normSq)
  have hns := Complex.mul_conj (Complex.Gamma s)
  rw [hns] at hrefl
  -- hrefl: ↑(normSq Γ(s)) = ↑π / ↑cosh(πt) = ↑(π/cosh(πt)):取 re
  have hfin : Complex.normSq (Complex.Gamma s) = Real.pi / Real.cosh (Real.pi * t) := by
    have hre := congrArg Complex.re hrefl
    -- hre: normSq = (↑π/↑cosh).re ⟹ 合并 cast 除法 + re 穿透
    have hdiv : (↑Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ)
        = (↑(Real.pi / Real.cosh (Real.pi * t)) : ℂ) := by
      exact (Complex.ofReal_div Real.pi (Real.cosh (Real.pi * t))).symm
    rw [hdiv] at hre
    -- hre: normSq = (↑(π/cosh)).re ⟹ 只展开 re (不展开 cast 内部)
    rw [Complex.ofReal_re] at hre
    exact hre
  -- 目标 ‖Γ(s)‖² = π/cosh(πt): normSq = ‖·‖²
  simpa [s, Complex.normSq_eq_norm_sq] using hfin


/-- χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): 函数方程乘子 (显式相位)。 -/
def chi (s : ℂ) : ℂ :=
  2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
    Complex.sin (↑Real.pi * s / 2)

-- arg(2π) ≠ π (conj_cpow 的条件: 底数不在负实轴)
private lemma arg_two_pi_ne_pi : ((2 * ↑Real.pi : ℂ).arg) ≠ Real.pi := by
  have h0 : (2 * ↑Real.pi : ℂ).arg = 0 := by
    have h0' : ((2 * Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (by positivity)
    simpa using h0'
  rw [h0]
  exact Real.pi_ne_zero.symm

-- conj 穿透 cpow (2π 底数, 正实数)
private lemma conj_two_pi_cpow (z : ℂ) :
    (starRingEnd ℂ) ((2 * ↑Real.pi : ℂ) ^ z) = (2 * ↑Real.pi : ℂ) ^ ((starRingEnd ℂ) z : ℂ) := by
  have h := Complex.conj_cpow (2 * ↑Real.pi : ℂ) z arg_two_pi_ne_pi
  have hc : (starRingEnd ℂ) (2 * ↑Real.pi : ℂ) = 2 * ↑Real.pi := by
    have hcast : (2 * ↑Real.pi : ℂ) = (↑(2 * Real.pi : ℝ) : ℂ) := by norm_num
    rw [hcast]
    exact Complex.conj_ofReal (2 * Real.pi)
  rw [hc] at h
  have h' := congrArg (starRingEnd ℂ) h.symm
  simpa using h'.symm

/-- ζ(s) = χ(s)·conj ζ(s), s = 1/2+it (函数方程 + mathlib 全域共轭)。 -/
theorem zeta_eq_chi_mul_conj_on_line (t : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = 2 * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ) *
          Complex.Gamma (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2) *
          (starRingEnd ℂ) (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have h1s : 1 - s = (starRingEnd ℂ) s := by
    dsimp [s]
    apply Complex.ext <;> simp <;> ring
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
  have hfe' := congrArg (starRingEnd ℂ) hfe
  have hfe'' : riemannZeta s = 2 * (2 * ↑Real.pi) ^ (-(starRingEnd ℂ) s) *
      Complex.Gamma ((starRingEnd ℂ) s) * Complex.cos (↑Real.pi * (starRingEnd ℂ) s / 2) *
      riemannZeta ((starRingEnd ℂ) s) := by
    have h2c : (starRingEnd ℂ) 2 = 2 := by exact Complex.conj_ofReal 2
    simpa [h2c, ← Complex.Gamma_conj, ← Complex.cos_conj, ← riemannZeta_conj, conj_two_pi_cpow]
      using hfe'
  rw [← h1s] at hfe''
  have hneg : -(1 - s) = (s - 1 : ℂ) := by ring
  rw [hneg] at hfe''
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) = Complex.sin (↑Real.pi * s / 2) := by
    rw [← Complex.cos_sub_pi_div_two]
    have harg : ↑Real.pi * (1 - s) / 2 = -((↑Real.pi * s / 2) - ↑Real.pi / 2) := by
      dsimp [s]; ring
    rw [harg, Complex.cos_neg]
  rw [hcos] at hfe''
  have hzeta_arg : riemannZeta (1 - s) = riemannZeta ((starRingEnd ℂ) s) := by rw [h1s]
  rw [hzeta_arg] at hfe''
  rw [riemannZeta_conj s] at hfe''
  dsimp [s] at hfe''
  exact hfe''

/-- u² = χ: u(t) = ζ(s)/|ζ(s)| 满足 u² = χ(s) (s = 1/2+it)。
    ζ = χ·conj ζ ⟹ |ζ|² = χ·(conj ζ)² ⟹ 1 = χ·(conj u)² ⟹ u² = χ (u·conj u = 1)。
    u 是 χ 的连续平方根 — 相位调制的映射相位关系。 -/
theorem zeta_unit_sq_eq_chi (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) ^ 2
      = 2 * (2 * ↑Real.pi) ^ (((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 : ℂ) *
          Complex.Gamma (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let u : ℂ := riemannZeta s / ‖riemannZeta s‖
  have hmain := zeta_eq_chi_mul_conj_on_line t
  have h2 : (‖riemannZeta s‖ : ℂ) ^ 2 =
      2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
        Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s) *
        (starRingEnd ℂ) (riemannZeta s) := by
    calc
      (‖riemannZeta s‖ : ℂ) ^ 2 = (↑(‖riemannZeta s‖ ^ 2) : ℂ) := by
        exact (map_pow Complex.ofRealHom (‖riemannZeta s‖) 2).symm
      _ = (Complex.normSq (riemannZeta s) : ℂ) := by
        rw [← Complex.normSq_eq_norm_sq]
      _ = riemannZeta s * (starRingEnd ℂ) (riemannZeta s) := by
        rw [← Complex.mul_conj]
      _ = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s)) *
          (starRingEnd ℂ) (riemannZeta s) := by
        exact congrArg (fun x : ℂ => x * (starRingEnd ℂ) (riemannZeta s)) hmain
  have hz_norm : (‖riemannZeta s‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have h1 : (1 : ℂ) = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2 := by
    calc
      1 = (‖riemannZeta s‖ : ℂ) ^ 2 / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        field_simp [hz_norm]
      _ = (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
            Complex.sin (↑Real.pi * s / 2) * (starRingEnd ℂ) (riemannZeta s) *
            (starRingEnd ℂ) (riemannZeta s)) / (‖riemannZeta s‖ : ℂ) ^ 2 := by
        rw [h2]
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) (riemannZeta s) / (‖riemannZeta s‖ : ℂ)) ^ 2 := by
        ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2 := by
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
  have hu2 : u ^ 2 = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
      Complex.sin (↑Real.pi * s / 2) := by
    have hu1' : (starRingEnd ℂ) u * u = 1 := by rw [← hu1]; ring
    calc
      u ^ 2 = u ^ 2 * ((starRingEnd ℂ) u * u) := by
        rw [hu1']
        ring
      _ = u ^ 2 * (u * (starRingEnd ℂ) u) := by
        ring
      _ = (u * (starRingEnd ℂ) u) * u ^ 2 := by
        ring
      _ = u ^ 2 := by
        rw [hu1]
        ring
      _ = (u ^ 2) * 1 := by ring
      _ = (u ^ 2) * (2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * ((starRingEnd ℂ) u) ^ 2) := by
        rw [← h1]
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * (u * (starRingEnd ℂ) u) ^ 2 := by
        ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) * 1 := by
        rw [hu1]
        ring
      _ = 2 * (2 * ↑Real.pi) ^ (s - 1 : ℂ) * Complex.Gamma (1 - s) *
          Complex.sin (↑Real.pi * s / 2) := by
        ring
  dsimp [u, s] at hu2
  exact hu2

/-- χ 沿临界线非零。 -/
lemma chi_ne_zero_on_line (t : ℝ) :
    chi ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) ≠ 0 := by
  dsimp [chi]
  refine mul_ne_zero ?_ ?_
  · refine mul_ne_zero ?_ ?_
    · refine mul_ne_zero ?_ ?_
      · norm_num
      · have h2pi : (2 * ↑Real.pi : ℂ) ≠ 0 :=
          mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
        exact (cpow_ne_zero_iff.mpr (Or.inl h2pi))
    · exact Complex.Gamma_ne_zero_of_re_pos (by
        rw [Complex.sub_re, Complex.add_re, Complex.mul_re]
        simp
        norm_num)
  · rw [Complex.sin_ne_zero_iff]
    intro k hk
    have hπ : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hπ0 : (↑Real.pi : ℂ) *
        (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 - (k : ℂ)) = 0 := by
      rw [mul_sub]
      have hπhalf : (↑Real.pi : ℂ) * (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2) =
          (↑Real.pi : ℂ) * ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 := by
        ring
      rw [hπhalf, hk]
      ring
    have hsub : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 - (k : ℂ) = 0 :=
      (mul_eq_zero.mp hπ0).resolve_left hπ
    have hs2 : (1 / 2 : ℂ) + (t : ℝ) * Complex.I = (2 : ℂ) * (k : ℂ) := by
      calc
        (1 / 2 : ℂ) + (t : ℝ) * Complex.I =
            (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2) * 2 := by ring
        _ = (k : ℂ) * 2 := by
          rw [show ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2 = (k : ℂ)
            by simpa [sub_eq_zero] using hsub]
        _ = 2 * (k : ℂ) := by ring
    have hre0 : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by
      rw [Complex.add_re, Complex.mul_re]
      simp
    have hre1 : ((2 : ℂ) * (k : ℂ)).re = 2 * (k : ℝ) := by simp
    have hEq : (1 / 2 : ℝ) = 2 * (k : ℝ) := by
      have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re =
          ((2 : ℂ) * (k : ℂ)).re := by
        rw [hs2]
      rw [hre0, hre1] at hre
      exact hre
    have hEq' : (4 * (k : ℤ) : ℤ) = 1 := by
      have h4 : (4 * (k : ℝ) : ℝ) = 1 := by nlinarith [hEq]
      exact_mod_cast h4
    omega

/-- 提升起点 y₀ = log χ(1/2)。 -/
noncomputable def theta0 (_T : ℝ) : ℂ :=
  Complex.log (chi ((1 / 2 : ℂ) + (0 : ℝ) * Complex.I))

lemma exp_theta0 (T : ℝ) :
    Complex.exp (theta0 T) = chi ((1 / 2 : ℂ) + (0 : ℝ) * Complex.I) := by
  dsimp [theta0]
  exact Complex.exp_log (chi_ne_zero_on_line 0)

/-- χ 沿临界线连续: 幂 (底 2π ∈ slitPlane) / Γ (1-s 非负整数) / sin 逐项连续。 -/
lemma continuousOn_chi_line : ContinuousOn chi {s : ℂ | s.re = 1 / 2} := by
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
      change ContinuousAt ((fun _ : ℂ => (1 : ℂ)) - _root_.id) s
      exact continuousAt_const.sub continuousAt_id
    exact (ContinuousAt.comp (continuousAt_Gamma (1 - s) (by
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
      (continuous_sin.comp hlin).continuousOn
  change ContinuousOn
    (fun s : ℂ =>
      2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.sin (↑Real.pi * s / 2))
    {s | s.re = 1 / 2}
  exact ((continuousOn_const.mul hpow).mul hΓ).mul hsin

/-- χ 沿临界线在 [0,1] 上的路径。 -/
def chiPath (T : ℝ) : C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨chi ((1 / 2 : ℂ) + ((T * s.1 : ℝ) : ℂ) * Complex.I),
    chi_ne_zero_on_line (T * s.1)⟩
  continuous_toFun := by
    have hsfun : Continuous (fun s : ℝ => (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hpath : Continuous (fun s : ℝ => chi ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)) := by
      rw [← continuousOn_univ]
      exact continuousOn_chi_line.comp hsfun.continuousOn (by intro s hs; simp)
    exact Continuous.subtype_mk (hpath.comp continuous_subtype_val)
      (fun s => chi_ne_zero_on_line (T * s.1))

/-- liftPath 的起点条件。 -/
private lemma liftPath_γ0 (T : ℝ) :
    chiPath T 0 = (⟨Complex.exp (theta0 T), Complex.exp_ne_zero (theta0 T)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  dsimp [chiPath]
  have hzero : ((T * (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ) := by
    simp
  rw [hzero]
  simpa using (exp_theta0 T).symm

/-- χ 的连续幅角提升: exp(θ(s)) = χ(1/2 + T·s·i)。 -/
noncomputable def thetaLift (T : ℝ) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (chiPath T) (theta0 T) (liftPath_γ0 T)

/-- 提升性质。 -/
lemma thetaLift_lifts (T : ℝ) (s : unitInterval) :
    Complex.exp (thetaLift T s) = chi ((1 / 2 : ℂ) + ((T * s.1 : ℝ) : ℂ) * Complex.I) := by
  have h := (isCoveringMap_exp.liftPath_lifts (chiPath T) (theta0 T) (liftPath_γ0 T))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [thetaLift]
  simpa [chiPath] using hs

/-- u 沿临界线的路径 (无零点区间)。 -/
def uPath (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    C(unitInterval, {z : ℂ // z ≠ 0}) where
  toFun s := ⟨riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
      ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖,
    by
      exact div_ne_zero (hz s)
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz s)))⟩
  continuous_toFun := by
    have hsfun : Continuous (fun s : ℝ => (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hzeta : Continuous (fun s : ℝ => riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)) := by
      rw [← continuousOn_univ]
      exact differentiableOn_riemannZeta.continuousOn.comp hsfun.continuousOn
        (by
          intro s hs h1
          have h1' : (1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I = 1 := h1
          have hre : ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I).re = 1 := by
            rw [h1']
            simp
          have hre' : ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I).re = 1 / 2 := by
            simp
          rw [hre'] at hre
          norm_num at hre)
    have hnorm : Continuous (fun s : ℝ => (‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖ : ℂ)) := by
      have hc : Continuous (fun s : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖) :=
        hzeta.norm
      exact continuous_ofReal.comp hc
    have hunitOn : ContinuousOn (fun s : ℝ =>
        riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I) /
          ‖riemannZeta ((1 / 2 : ℂ) + ((T * s : ℝ) : ℂ) * Complex.I)‖) (Set.Icc 0 1) := by
      refine hzeta.continuousOn.div hnorm.continuousOn ?_
      intro s hs
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz ⟨s, hs⟩))
    have hunit : Continuous (fun s : unitInterval =>
        riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
          ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖) :=
      hunitOn.restrict
    exact Continuous.subtype_mk hunit
      (fun s => div_ne_zero (hz s) (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hz s))))

/-- u 的提升起点。 -/
noncomputable def uLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : ℂ :=
  Complex.log ((uPath T hz 0 : {z : ℂ // z ≠ 0}).1)

lemma exp_uLift0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    Complex.exp (uLift0 T hz) = (uPath T hz 0 : {z : ℂ // z ≠ 0}).1 := by
  dsimp [uLift0]
  exact Complex.exp_log (uPath T hz 0).2

/-- liftPath 的起点条件。 -/
private lemma uLift_γ0 (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    uPath T hz 0 = (⟨Complex.exp (uLift0 T hz), Complex.exp_ne_zero (uLift0 T hz)⟩ : {z : ℂ // z ≠ 0}) := by
  ext
  exact (exp_uLift0 T hz).symm

/-- u 的连续幅角提升。 -/
noncomputable def uLift (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz)

/-- 提升性质。 -/
lemma uLift_lifts (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) (s : unitInterval) :
    Complex.exp (uLift T hz s) =
      riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I)‖ := by
  have h := (isCoveringMap_exp.liftPath_lifts (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz))
  have hs := congrArg (fun f : unitInterval → {z : ℂ // z ≠ 0} => (f s : ℂ)) h
  dsimp [uLift]
  simpa [uPath] using hs

/-- exp 的核: exp z = 1。 -/
def expKernel : Set ℂ := {z | Complex.exp z = 1}

/-- expKernel = 2πiℤ。 -/
lemma expKernel_mem_iff (z : ℂ) :
    z ∈ expKernel ↔ ∃ n : ℤ, z = (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  rw [expKernel]
  constructor
  · intro hz
    have he : Complex.exp z = Complex.exp 0 := by simpa using hz
    rcases (exp_eq_exp_iff_exists_int.mp he) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa using hn
  · rintro ⟨n, rfl⟩
    change Complex.exp (n * (2 * ↑Real.pi * Complex.I)) = 1
    rw [← Complex.exp_zero, exp_eq_exp_iff_exists_int]
    exact ⟨n, by ring⟩

/-- u² = χ (T5): 无零点处 (ζ/‖ζ‖)² = χ (def chi 形式)。 -/
lemma zeta_unit_sq_eq_chi_short (t : ℝ)
    (hz : riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) ≠ 0) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) /
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ : ℂ) ^ 2 = chi ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) := by
  simpa [chi] using (zeta_unit_sq_eq_chi t hz)

/-- **S(T) 的整数层结构**: θ_ζ - θ_χ/2 ∈ πiℤ 逐点 —
    符号改变 (翻转 ±1) 但位置 (零点) 不变 = pat 正负 1 过程。
    整数层 = 2πi 的迭代计数 (i 的迭代), θ_χ 显式 (快路径)。 -/
theorem zeta_lift_half_chi_lift_pi_int (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0)
    (s : unitInterval) :
    ∃ n : ℤ, uLift T hz s - thetaLift T s / 2 = (n : ℂ) * (↑Real.pi * Complex.I) := by
  -- 2θ_ζ - θ_χ ∈ expKernel = 2πiℤ (从 u² = χ: exp(2θ_ζ) = u² = χ = exp(θ_χ))
  have hk : 2 * uLift T hz s - thetaLift T s ∈ expKernel := by
    rw [expKernel]
    change Complex.exp (2 * uLift T hz s - thetaLift T s) = 1
    rw [Complex.exp_sub]
    have h2e : Complex.exp (2 * uLift T hz s) = (Complex.exp (uLift T hz s)) ^ 2 := by
      rw [show (2 : ℂ) * uLift T hz s = uLift T hz s + uLift T hz s by ring]
      rw [Complex.exp_add]
      ring
    rw [h2e]
    rw [uLift_lifts, thetaLift_lifts]
    -- u² = χ (T5)
    rw [zeta_unit_sq_eq_chi_short (T * s.1) (hz s)]
    exact div_self (chi_ne_zero_on_line (T * s.1))
  -- 2θ_ζ - θ_χ = 2πi·n ⟹ θ_ζ - θ_χ/2 = πi·n
  rcases (expKernel_mem_iff (2 * uLift T hz s - thetaLift T s)).1 hk with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- hn : 2θ_ζ - θ_χ = n·2πi
  -- 目标: θ_ζ - θ_χ/2 = n·πi
  calc
    uLift T hz s - thetaLift T s / 2 = (2 * uLift T hz s - thetaLift T s) / 2 := by ring
    _ = (n : ℂ) * (2 * ↑Real.pi * Complex.I) / 2 := by rw [hn]
    _ = (n : ℂ) * (↑Real.pi * Complex.I) := by ring


/-- **周期发散桥 (反转对接)**: 2·Δθ_ζ = Δθ_χ + 2πi·m —
    每翻转一次 (u → -u, 离散 ±1) χ 转一整圈 (连续 2π)。 -/
theorem flip_chi_circle_bridge (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    ∃ m : ℤ, 2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)
      = (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  rcases (zeta_lift_half_chi_lift_pi_int T hz 1) with ⟨n1, h1⟩
  rcases (zeta_lift_half_chi_lift_pi_int T hz 0) with ⟨n0, h0⟩
  refine ⟨n1 - n0, ?_⟩
  -- h1 : θ_ζ(1) - θ_χ(1)/2 = n1·πi; h0 : θ_ζ(0) - θ_χ(0)/2 = n0·πi
  -- 2Δθ_ζ - Δθ_χ = 2·[(θ_ζ(1)-θ_χ(1)/2) - (θ_ζ(0)-θ_χ(0)/2)]
  calc
    2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)
        = 2 * ((uLift T hz 1 - thetaLift T 1 / 2) - (uLift T hz 0 - thetaLift T 0 / 2)) := by ring
    _ = 2 * ((n1 : ℂ) * (↑Real.pi * Complex.I) - (n0 : ℂ) * (↑Real.pi * Complex.I)) := by
      rw [h1, h0]
    _ = ((n1 - n0 : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast
      ring

/-- **连续离散逆桥**: 净翻转 m = (2·Δθ_ζ - Δθ_χ)/(2πi) ∈ ℤ —
    从连续提升的端点差重构离散翻转计数。 -/
theorem net_flip_from_chi_lift (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    ∃ m : ℤ, ((2 * (uLift T hz 1 - uLift T hz 0) - (thetaLift T 1 - thetaLift T 0)) /
      (2 * ↑Real.pi * Complex.I)) = (m : ℂ) := by
  rcases (flip_chi_circle_bridge T hz) with ⟨m, hm⟩
  rw [hm]
  -- (m·2πi)/(2πi) = m ∈ ℤ
  have h2pi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (by exact_mod_cast (Real.pi_ne_zero) : (↑Real.pi : ℂ) ≠ 0)) Complex.I_ne_zero
  rw [show (m : ℂ) * (2 * ↑Real.pi * Complex.I) / (2 * ↑Real.pi * Complex.I) = (m : ℂ) by
    exact mul_div_cancel_right₀ (m : ℂ) h2pi]
  exact ⟨m, rfl⟩


lemma thetaLift_zero (T : ℝ) :
    thetaLift T 0 = theta0 T := by
  exact isCoveringMap_exp.liftPath_zero (chiPath T) (theta0 T) (liftPath_γ0 T)


/-- 素数因子零点定理: 1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s·ln p = k·2πi。
    每个素数因子 (1-p^{-s}) 的零点全在 Re(s) = 0 上 (纯虚轴) —
    "素数复数进制分解"的精确内容 (Complex.exp_eq_one_iff)。
    (副本: proof.lean 同定理, 隔离文件自包含依赖) -/
theorem prime_factor_zero (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    (1 - (p : ℂ) ^ (-s) = 0) ↔
      ∃ k : ℤ, s * Complex.log (p : ℂ) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
  constructor
  · intro h
    have hpow : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    rw [Complex.cpow_def_of_ne_zero hp0] at hpow
    rcases (Complex.exp_eq_one_iff).1 hpow with ⟨n, hn⟩
    use -n
    -- 从 hn: log p · (-s) = n·2πi 推出 s·log p = (-n)·2πi = ↑(-n)·2πi
    calc
      s * Complex.log (p : ℂ) = -((-s) * Complex.log (p : ℂ)) := by ring
      _ = -((n : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
        rw [show (-s) * Complex.log (p : ℂ) = (n : ℂ) * (2 * ↑Real.pi * Complex.I) by
          simpa [mul_comm] using hn]
      _ = (-(n : ℂ)) * (2 * ↑Real.pi * Complex.I) := by rw [← neg_mul]
      _ = (↑(-n) : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [Int.cast_neg]
  · rintro ⟨k, hk⟩
    rw [Complex.cpow_def_of_ne_zero hp0]
    rw [sub_eq_zero]
    symm
    apply (Complex.exp_eq_one_iff).mpr
    refine ⟨-k, ?_⟩
    -- 目标: log p · (-s) = ↑(-k)·2πi; 从 hk: s·log p = k·2πi
    calc
      Complex.log (p : ℂ) * (-s) = -((s) * Complex.log (p : ℂ)) := by ring
      _ = -((k : ℂ) * (2 * ↑Real.pi * Complex.I)) := by rw [hk]
      _ = (-(k : ℂ)) * (2 * ↑Real.pi * Complex.I) := by rw [← neg_mul]
      _ = (↑(-k) : ℂ) * (2 * ↑Real.pi * Complex.I) := by rw [Int.cast_neg]

/-- 拆分恒等式: ζ = 奇部分 + 偶部分 (任意基点 p ≠ 0, 代数拆分). -/
theorem zeta_eq_odd_add_even (p : ℂ) (s : ℂ) :
    riemannZeta s = (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s
      + (p : ℂ) ^ (-s : ℂ) * riemannZeta s := by
  ring

/-- 零点 = 奇偶公共零点: ζ(s) = 0 ⟺ O_p(s) = 0 ∧ E_p(s) = 0 (任意基点 p ≠ 0).
    奇侧偶侧同时为 0 (用户: "奇偶同时为 0") 的精确形式. -/
theorem zeta_eq_zero_iff_p_split {p : ℂ} (hp : p ≠ 0) (s : ℂ) :
    riemannZeta s = 0 ↔
      (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 ∧
        (p : ℂ) ^ (-s : ℂ) * riemannZeta s = 0 := by
  constructor
  · intro hz
    constructor <;> simp [hz]
  · intro h
    have hpz : (p : ℂ) ^ (-s : ℂ) ≠ 0 := by
      exact (Complex.cpow_ne_zero_iff).mpr (Or.inl hp)
    -- 偶部分 E_p = p⁻ˢ·ζ = 0 且 p⁻ˢ ≠ 0 ⟹ ζ = 0 (ℂ 是域)
    exact (mul_eq_zero.mp h.2).resolve_left hpz

/-- 奇部分零点分解: O_p = 0 ⟺ ζ = 0 ∨ p⁻ˢ = 1 (ℂ 域乘法为零).
    奇部分的零点 = ζ 零点 ∪ 素数因子零点. -/
theorem p_split_mul_zero_iff {p : ℂ} (hp : p ≠ 0) (s : ℂ) :
    (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 ↔
      riemannZeta s = 0 ∨ (p : ℂ) ^ (-s : ℂ) = 1 := by
  rw [mul_eq_zero, sub_eq_zero]
  tauto

/-- 奇部分独有零点全在虚轴 (p = 2 奇偶拆分):
    若 O₂(s) = 0 且 ζ(s) ≠ 0, 则 2⁻ˢ = 1 ⟹ s·ln 2 ∈ 2πiℤ ⟹ Re s = 0.
    即奇偶拆分的非公共零点不进入临界带 — 交点只能来自 ζ 本身. -/
theorem odd_part_extra_zero_on_imag_axis (s : ℂ) :
    (1 - (2 : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 → riemannZeta s ≠ 0 → s.re = 0 := by
  intro h hz
  have hcases := (p_split_mul_zero_iff (p := (2 : ℂ)) (by norm_num) s).mp h
  rcases hcases with hz' | hone
  · exact False.elim (hz hz')
  · -- 2⁻ˢ = 1 ⟹ 1 - 2⁻ˢ = 0 ⟹ (prime_factor_zero 2) ∃k, s·log 2 = 2πik
    have hsub : 1 - (2 : ℂ) ^ (-s : ℂ) = 0 := sub_eq_zero.mpr hone.symm
    have hp2 : Nat.Prime 2 := Nat.prime_two
    have hpf := (prime_factor_zero 2 hp2 s).mp hsub
    rcases hpf with ⟨k, hk⟩
    -- Re(s·log 2) = Re(k·2πi) = 0; log 2 是实数且非零 ⟹ s.re = 0
    have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
      exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    have hre0 : (s * Complex.log (2 : ℂ)).re = 0 := by
      have hk' : s * Complex.log ((2 : ℂ)) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
        simpa using hk
      rw [hk']
      simp
    have hre' : s.re * Real.log 2 = 0 := by
      calc
        s.re * Real.log 2 = (s * (Real.log 2 : ℂ)).re := by
          rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero]
        _ = 0 := by rw [← hlog, hre0]
    have hl2 : Real.log 2 ≠ 0 := by
      exact (Real.log_ne_zero).mpr (by norm_num)
    exact (mul_eq_zero.mp hre').resolve_right hl2


lemma uLift_zero (T : ℝ) (hz : ∀ s : unitInterval,
    riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    uLift T hz 0 = uLift0 T hz := by
  exact isCoveringMap_exp.liftPath_zero (uPath T hz) (uLift0 T hz) (uLift_γ0 T hz)

lemma expKernel_dist_ge_two_pi {z w : ℂ} (hz : z ∈ expKernel) (hw : w ∈ expKernel)
    (hzw : z ≠ w) : 2 * Real.pi ≤ ‖z - w‖ := by
  rcases (expKernel_mem_iff z).1 hz with ⟨n, rfl⟩
  rcases (expKernel_mem_iff w).1 hw with ⟨m, rfl⟩
  have hn0 : n ≠ m := by
    intro hnm
    apply hzw
    rw [hnm]
  have hnm1 : (1 : ℝ) ≤ |(n - m : ℤ)| := by
    exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hn0))
  calc
    2 * Real.pi ≤ |((n - m : ℤ) : ℝ)| * (2 * Real.pi) := by
      have hnm1' : (1 : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by
        simpa [Int.cast_abs] using hnm1
      nlinarith [hnm1', Real.pi_pos]
    _ = ‖((n - m : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)‖ := by
      rw [Complex.norm_mul]
      have hnorm : ‖(2 * ↑Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
        rw [show (2 * ↑Real.pi * Complex.I : ℂ) = (2 * ↑Real.pi : ℂ) * Complex.I by ring]
        rw [Complex.norm_mul]
        have hcast : (2 * ↑Real.pi : ℂ) = (↑(2 * Real.pi : ℝ) : ℂ) := by norm_num
        rw [hcast]
        have hn2 : ‖(↑(2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
          exact (RCLike.norm_ofReal (2 * Real.pi)).trans
            (abs_of_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)))
        rw [hn2, Complex.norm_I]
        ring
      rw [Complex.norm_intCast, hnorm]
    _ = ‖(n : ℂ) * (2 * ↑Real.pi * Complex.I) - (m : ℂ) * (2 * ↑Real.pi * Complex.I)‖ := by
      congr 1
      rw [← sub_mul]
      congr 1
      simp

/-- expKernel 的诱导拓扑离散 (每点孤立: 间距 2π > 半径 π 的开球)。 -/
instance expKernel_discrete : DiscreteTopology {z : ℂ // z ∈ expKernel} := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro z
  -- {z} = ball z.1 π ∩ expKernel (诱导拓扑的开集)
  refine ⟨Metric.ball (z : ℂ) Real.pi, Metric.isOpen_ball, ?_⟩
  apply Set.ext
  intro w
  change w ∈ Subtype.val ⁻¹' Metric.ball (z.1 : ℂ) Real.pi ↔ w = z
  constructor
  · intro hw
    apply Subtype.ext
    by_contra hne
    have hd : 2 * Real.pi ≤ ‖w.1 - z.1‖ :=
      expKernel_dist_ge_two_pi w.2 z.2 hne
    have hlt : ‖w.1 - z.1‖ < Real.pi := by
      rw [← dist_eq_norm]
      exact hw
    nlinarith [hd, hlt, Real.pi_pos]
  · intro hw
    rw [hw]
    have hself : z.1 ∈ Metric.ball (z.1 : ℂ) Real.pi :=
      Metric.mem_ball_self Real.pi_pos
    simpa [dist_eq_norm] using hself

/-- **相位对齐 (预言/召唤的对称映射)**: 无零点区间 [0,T] 上,
    u² = χ (T5) ⟹ exp(2θ_ζ) = exp(θ_χ) ⟹ 2θ_ζ - θ_χ ∈ expKernel 常数 ⟹
    2·(θ_ζ(T) - θ_ζ(0)) = θ_χ(T) - θ_χ(0)。
    起点 (显式 χ 相位) 与终点 (θ_ζ 端点差) 之间的映射相位关系直接锁定,
    不需要迭代逼近。 -/
theorem phase_align_two_zeta_lift_eq_chi_lift (T : ℝ)
    (hz : ∀ s : unitInterval, riemannZeta ((1 / 2 : ℂ) + (T * s.1 : ℝ) * Complex.I) ≠ 0) :
    2 * (uLift T hz 1 - uLift T hz 0) = thetaLift T 1 - thetaLift T 0 := by
  let f : unitInterval → ℂ := fun s => 2 * uLift T hz s - thetaLift T s
  have hk : ∀ s : unitInterval, f s ∈ expKernel := by
    intro s
    rw [expKernel]
    dsimp [f]
    rw [Complex.exp_sub]
    have h2e : Complex.exp (2 * uLift T hz s) = (Complex.exp (uLift T hz s)) ^ 2 := by
      rw [show (2 : ℂ) * uLift T hz s = uLift T hz s + uLift T hz s by ring]
      rw [Complex.exp_add]
      ring
    rw [h2e]
    rw [uLift_lifts, thetaLift_lifts]
    rw [zeta_unit_sq_eq_chi (T * s.1) (hz s)]
    exact div_self (chi_ne_zero_on_line (T * s.1))
  let f' : unitInterval → {z : ℂ // z ∈ expKernel} := fun s => ⟨f s, hk s⟩
  have hf' : Continuous f' := by
    have hf : Continuous f := by
      dsimp [f]
      exact (continuous_const.mul (uLift T hz).continuous).sub (thetaLift T).continuous
    exact Continuous.subtype_mk hf (fun s => hk s)
  have hc : f' 0 = f' 1 :=
    IsPreconnected.constant (s := Set.univ) (isPreconnected_univ)
      hf'.continuousOn (by trivial) (by trivial)
  have hf01 : f 0 = f 1 := by
    have := congrArg Subtype.val hc
    simpa using this
  dsimp [f] at hf01
  -- hf01 : 2·u0 - t0 = 2·u1 - t1 ⟹ 目标 2(u1-u0) = t1-t0
  calc
    2 * (uLift T hz 1 - uLift T hz 0)
        = 2 * uLift T hz 1 - 2 * uLift T hz 0 := by ring
    _ = (2 * uLift T hz 1 - thetaLift T 1) + (thetaLift T 1 - 2 * uLift T hz 0) := by ring
    _ = (2 * uLift T hz 0 - thetaLift T 0) + (thetaLift T 1 - 2 * uLift T hz 0) := by
      rw [← hf01]
    _ = thetaLift T 1 - thetaLift T 0 := by ring


/-- 正实数的 cpow 共轭: conj(t^w) = t^(conj w) 对 t > 0 (arg = 0). -/
lemma conj_cpow_of_pos {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (starRingEnd ℂ) ((t : ℂ) ^ (w : ℂ)) = (t : ℂ) ^ ((starRingEnd ℂ) w : ℂ) := by
  have harg : ((t : ℂ)).arg ≠ Real.pi := by
    have h0 : ((t : ℂ)).arg = 0 := by
      have h0' : ((t : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (le_of_lt ht)
      simpa using h0'
    rw [h0]
    exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (t : ℂ) w harg
  have htc : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by
    exact Complex.conj_ofReal t
  rw [htc] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa using h'

/-- f_modif (hurwitzEvenFEPair 0) 实值: evenKernel 实值 (ofReal 嵌入) + 系数全实. -/
lemma conj_f_modif_zero (t : ℝ) :
    (starRingEnd ℂ) ((hurwitzEvenFEPair 0).f_modif t) = (hurwitzEvenFEPair 0).f_modif t := by
  unfold WeakFEPair.f_modif
  rw [Pi.add_apply, map_add]
  -- 项 1: indicator (Ioi 1) (fun x => f x - f₀)
  have h1 : (starRingEnd ℂ)
      ((Ioi (1 : ℝ)).indicator (fun x : ℝ => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀) t)
      = (Ioi (1 : ℝ)).indicator (fun x : ℝ => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀) t := by
    rw [map_indicator]
    congr 1
    funext x
    simp [hurwitzEvenFEPair]
  -- 项 2: indicator (Ioo 0 1) (fun x => f x - (ε * ↑(x ^ (-k))) • g₀)
  have h2 : (starRingEnd ℂ)
      ((Ioo (0 : ℝ) 1).indicator (fun x : ℝ =>
        (hurwitzEvenFEPair 0).f x - ((hurwitzEvenFEPair 0).ε * ↑(x ^ (-(hurwitzEvenFEPair 0).k))) • (hurwitzEvenFEPair 0).g₀) t)
      = (Ioo (0 : ℝ) 1).indicator (fun x : ℝ =>
        (hurwitzEvenFEPair 0).f x - ((hurwitzEvenFEPair 0).ε * ↑(x ^ (-(hurwitzEvenFEPair 0).k))) • (hurwitzEvenFEPair 0).g₀) t := by
    rw [map_indicator]
    congr 1
    funext x
    simp [hurwitzEvenFEPair]
  rw [h1, h2]

/-- Mellin 共轭 (f_modif 实值, 积分共轭无条件): conj(mellin f w) = mellin f (conj w). -/
lemma conj_mellin_f_modif (w : ℂ) :
    (starRingEnd ℂ) (mellin (hurwitzEvenFEPair 0).f_modif w)
      = mellin (hurwitzEvenFEPair 0).f_modif ((starRingEnd ℂ) w) := by
  unfold mellin
  rw [← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
  rw [smul_eq_mul, smul_eq_mul]
  rw [map_mul]
  rw [conj_cpow_of_pos ht (w - 1)]
  rw [conj_f_modif_zero t]
  simp [map_sub]

/-- Λ₀ 共轭 (整函数定义层穿透): conj(completedRiemannZeta₀ s) = completedRiemannZeta₀ (conj s). -/
lemma conj_completedRiemannZeta₀ (s : ℂ) :
    (starRingEnd ℂ) (completedRiemannZeta₀ s) = completedRiemannZeta₀ (starRingEnd ℂ s) := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀
  rw [map_div₀]
  rw [map_ofNat]
  have hme : (starRingEnd ℂ) ((hurwitzEvenFEPair 0).Λ₀ (s / 2))
      = (hurwitzEvenFEPair 0).Λ₀ ((starRingEnd ℂ) s / 2) := by
    unfold WeakFEPair.Λ₀
    simpa [map_div₀, map_ofNat] using conj_mellin_f_modif (s / 2)
  rw [hme]

/-- 临界带 ζ 共轭: conj(ζ(s)) = ζ(conj s) 对 0 < Re s < 1.
    pat0 启发: 对称性接力 (Λ₀ 结构/函数方程) 替代解析延拓差分论证. -/
theorem zeta_conj_of_critical_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (starRingEnd ℂ) (riemannZeta s) = riemannZeta (starRingEnd ℂ s) := by
  have hs' : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    linarith [hs1]
  have hsneg : ∀ n : ℕ, s / 2 + 1 ≠ -↑n := by
    intro n h
    have hre : (s / 2 + 1).re = (-(↑n : ℂ)).re := by rw [h]
    have hre' : (s / 2 + 1).re = s.re / 2 + 1 := by
      rw [Complex.add_re, Complex.one_re]
      simp
    have hpos : 0 < s.re / 2 + 1 := by linarith [hs0]
    have hneg : ((-(↑n : ℂ)).re) ≤ 0 := by simp
    linarith
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcne : (↑Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl hpi)
  have hgam2 : Complex.Gamma (s / 2 + 1) ≠ 0 := by
    exact Complex.Gamma_ne_zero hsneg
  have hden : 2 * (↑Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hcne) hgam2
  -- 分母共轭: conj(2·π^(-s/2)·Γ(s/2+1)) = 2·π^(-conj s/2)·Γ(conj s/2+1)
  have harg_pi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
    have h0 : (↑Real.pi : ℂ).arg = 0 := by
      have h0' : ((Real.pi : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)
      simpa using h0'
    rw [h0]
    exact Real.pi_ne_zero.symm
  have hpi_conj : (starRingEnd ℂ) ((↑Real.pi : ℂ) ^ ((-s / 2) : ℂ))
      = (↑Real.pi : ℂ) ^ ((-(starRingEnd ℂ) s / 2) : ℂ) := by
    have h := Complex.conj_cpow (↑Real.pi : ℂ) (-s / 2 : ℂ) harg_pi
    have hpic : (starRingEnd ℂ) (↑Real.pi : ℂ) = ↑Real.pi := by
      exact Complex.conj_ofReal Real.pi
    rw [hpic] at h
    have h' := congrArg (starRingEnd ℂ) h
    simpa [map_div₀, map_neg, map_ofNat] using h'
  have hgamma_conj : (starRingEnd ℂ) (Complex.Gamma (s / 2 + 1))
      = Complex.Gamma ((starRingEnd ℂ) s / 2 + 1) := by
    have h := Complex.Gamma_conj (s / 2 + 1)
    rw [← h]
    congr 1
    simp [map_div₀, map_add, map_one, map_ofNat]
  -- 主证明: 对 riemannZeta_eq_mul_completedRiemannZeta₀ s 两边 conj
  have hfe := riemannZeta_eq_mul_completedRiemannZeta₀ s
  have hc := congrArg (starRingEnd ℂ) hfe
  rw [map_div₀] at hc
  -- 分子 conj: conj(s·Λ₀(s) − 1 − s/(1−s))
  have hnum : (starRingEnd ℂ) (s * completedRiemannZeta₀ s - 1 - s / (1 - s))
      = (starRingEnd ℂ) s * completedRiemannZeta₀ (starRingEnd ℂ s) - 1
        - (starRingEnd ℂ) s / (1 - (starRingEnd ℂ) s) := by
    rw [map_sub, map_sub, map_mul]
    rw [conj_completedRiemannZeta₀ s]
    rw [map_div₀]
    rw [map_sub]
    simp
  rw [hnum] at hc
  -- 分母 conj
  have hden_conj : (starRingEnd ℂ) (2 * (↑Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))
      = 2 * (↑Real.pi : ℂ) ^ (-(starRingEnd ℂ) s / 2) * Complex.Gamma ((starRingEnd ℂ) s / 2 + 1) := by
    rw [map_mul, map_mul]
    rw [map_ofNat]
    rw [hpi_conj]
    rw [hgamma_conj]
  rw [hden_conj] at hc
  -- 目标: conj(ζ(s)) = ζ(conj s); 展开 ζ(conj s) 用同一公式
  rw [riemannZeta_eq_mul_completedRiemannZeta₀ (starRingEnd ℂ s)]
  exact hc

/- ============ ζ 的实部/虚部拆分 (共轭投影) ============ -/

/-- 实部共轭对称: Re ζ(s) = Re ζ(conj s) (临界带, 假实轴部分偶). -/
theorem zeta_re_conj_symm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (riemannZeta s).re = (riemannZeta (starRingEnd ℂ s)).re := by
  have hz := zeta_conj_of_critical_strip (s := s) hs0 hs1
  have hr := congrArg Complex.re hz
  simpa using hr

/-- 虚部共轭反对称: Im ζ(s) = -Im ζ(conj s) (临界带, y 轴泄漏奇). -/
theorem zeta_im_conj_antisymm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (riemannZeta s).im = -(riemannZeta (starRingEnd ℂ s)).im := by
  have hz := zeta_conj_of_critical_strip (s := s) hs0 hs1
  have hi := congrArg Complex.im hz
  have hi' : -(riemannZeta s).im = (riemannZeta (starRingEnd ℂ s)).im := by
    simpa using hi
  linarith

/-- 临界线实部偶: Re ζ(1/2+it) = Re ζ(1/2-it). -/
theorem zeta_re_even_on_line (t : ℝ) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re
      = (riemannZeta ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re := by
  -- s = 1/2+it: conj s = 1/2-it
  have hs0 : 0 < ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re := by simp
  have hs1 : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re < 1 := by
    simp
    norm_num
  have hsym := zeta_re_conj_symm (s := (1 / 2 : ℂ) + (t : ℂ) * Complex.I) hs0 hs1
  -- hsym : re(ζ(1/2+it)) = re(ζ(conj(1/2+it)));conj(1/2+it) = 1/2-it:simpa
  -- conj 对加法分配得 `+ -(↑t*I)`, goal 是 `- ↑t*I`: sub_eq_add_neg 对齐
  simpa [Complex.conj_ofReal, Complex.conj_I, map_add, map_mul, map_inv₀, map_ofNat,
    sub_eq_add_neg] using hsym

/-- 临界线虚部奇: Im ζ(1/2+it) = -Im ζ(1/2-it). -/
theorem zeta_im_odd_on_line (t : ℝ) :
    (riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im
      = -((riemannZeta ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).im) := by
  have hs0 : 0 < ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re := by simp
  have hs1 : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re < 1 := by
    simp
    norm_num
  have hsym := zeta_im_conj_antisymm (s := (1 / 2 : ℂ) + (t : ℂ) * Complex.I) hs0 hs1
  simpa [Complex.conj_ofReal, Complex.conj_I, map_add, map_mul, map_inv₀, map_ofNat,
    sub_eq_add_neg] using hsym


theorem chi_conj (s : ℂ) : chi (conj s) = conj (chi s) := by
  unfold chi
  rw [map_mul, map_mul, map_mul]
  -- conj((2π)^{s-1}) = (2π)^{conj s - 1}: 底 2π 为正实数 (arg = 0 ≠ π)
  have hpow : conj ((2 * ↑Real.pi : ℂ) ^ (s - 1)) = (2 * ↑Real.pi : ℂ) ^ (conj s - 1) := by
    have hx : (2 * ↑Real.pi : ℂ).arg ≠ (Real.pi : ℝ) := by
      have hcast : (2 * ↑Real.pi : ℂ) = (2 * Real.pi : ℝ) := by norm_num
      have harg : (2 * ↑Real.pi : ℂ).arg = 0 := by
        rw [hcast, Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      rw [harg]
      exact Real.pi_ne_zero.symm
    have h1 := Complex.conj_cpow (2 * ↑Real.pi : ℂ) (conj s - 1) hx
    -- h1 : conj(2π)^(conj s - 1) = conj((2π)^(conj(conj s - 1)))
    -- 左 = (2π)^(conj s - 1), 右 = conj((2π)^(s-1))
    simpa [map_ofNat, Complex.conj_ofReal, conj_conj, map_sub, map_one] using h1.symm
  rw [hpow]
  -- Γ(1-s) 的共轭 = Γ(1 - conj s)
  have hgamma : conj (Complex.Gamma (1 - s)) = Complex.Gamma (1 - conj s) := by
    simpa [map_sub, map_one] using (Gamma_conj (1 - s)).symm
  rw [hgamma]
  -- sin(πs/2) 的共轭 = sin(π·conj s/2)
  have hsin : conj (Complex.sin (↑Real.pi * s / 2)) =
      Complex.sin (↑Real.pi * conj s / 2) := by
    simpa [map_div, map_mul, map_ofNat, Complex.conj_ofReal, conj_conj]
      using (sin_conj (↑Real.pi * s / 2)).symm
  rw [hsin]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [map_ofNat]
  rw [h2]

/-- **乘子自反**: χ(s)·χ(1-s) = 1 (s ∉ ℤ)。
    = 4(2π)^{-1}·Γ(1-s)Γ(s)·sin(πs/2)sin(π(1-s)/2)
    = 4(2π)^{-1}·(π/sin πs)·(1/2)sin πs = 1 (反射公式 + 积化和差)。 -/
theorem chi_mul_chi_one_sub {s : ℂ} (hs : s ∉ Set.range (fun n : ℤ => (n : ℂ))) :
    chi s * chi (1 - s) = 1 := by
  -- 重排: 4·(2π)^{s-1}(2π)^{-s}·Γ(1-s)Γ(s)·sin(πs/2)sin(π(1-s)/2)
  have h1 : chi s * chi (1 - s) =
      4 * ((2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (1 - s - 1)) *
        (Complex.Gamma (1 - s) * Complex.Gamma s) *
        (Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2)) := by
    unfold chi
    ring
  -- (2π)^{s-1}·(2π)^{(1-s)-1} = (2π)^{-1}
  have hne : (2 * ↑Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hpow : (2 * ↑Real.pi : ℂ) ^ (s - 1) * (2 * ↑Real.pi : ℂ) ^ (1 - s - 1) =
      (2 * ↑Real.pi : ℂ) ^ (-1 : ℂ) := by
    rw [← cpow_add (s - 1) (1 - s - 1) hne]
    congr 1
    ring
  -- Γ(1-s)·Γ(s) = π/sin(πs) (反射, 无条件)
  have hgamma : Complex.Gamma (1 - s) * Complex.Gamma s =
      ↑Real.pi / Complex.sin (↑Real.pi * s) := by
    simpa [mul_comm] using (Gamma_mul_Gamma_one_sub s)
  -- sin(πs/2)·sin(π(1-s)/2) = (1/2)sin(πs): 积化和差
  have hsin : Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2) =
      (1 / 2 : ℂ) * Complex.sin (↑Real.pi * s) := by
    -- cos(X-Y) - cos(X+Y) = 2 sin X sin Y, X = πs/2, Y = π(1-s)/2
    have hcc : Complex.cos (↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2) -
        Complex.cos (↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2) =
        2 * Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2) := by
      rw [Complex.cos_sub_cos]
      -- cos(X-Y) - cos(X+Y) = -2 sin X sin(-Y) = 2 sin X sin Y
      have harg : (↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2 -
          (↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2)) / 2 =
          -(↑Real.pi * (1 - s) / 2) := by ring
      rw [harg, Complex.sin_neg]
      ring
    have hcos1 : Complex.cos (↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2) =
        Complex.sin (↑Real.pi * s) := by
      have hsub : ↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2 = ↑Real.pi * s - ↑Real.pi / 2 := by
        ring
      rw [hsub, ← Complex.cos_sub_pi_div_two]
    have hcos2 : Complex.cos (↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2) = 0 := by
      have hadd : ↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2 = ↑Real.pi / 2 := by ring
      rw [hadd, Complex.cos_pi_div_two]
    calc
      Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2) =
          (1 / 2 : ℂ) * (2 * Complex.sin (↑Real.pi * s / 2) * Complex.sin (↑Real.pi * (1 - s) / 2)) := by
        ring
      _ = (1 / 2 : ℂ) * (Complex.cos (↑Real.pi * s / 2 - ↑Real.pi * (1 - s) / 2) -
          Complex.cos (↑Real.pi * s / 2 + ↑Real.pi * (1 - s) / 2)) := by
        rw [← hcc]
      _ = (1 / 2 : ℂ) * Complex.sin (↑Real.pi * s) := by
        rw [hcos1, hcos2]
        ring
  -- s ∉ ℤ ⟹ sin(πs) ≠ 0 (sin 零点恰在 πℤ)
  have hsne : Complex.sin (↑Real.pi * s) ≠ 0 := by
    intro hz
    rcases (Complex.sin_eq_zero_iff.mp hz) with ⟨k, hk⟩
    -- π·s = k·π ⟹ s = k (整数), 矛盾
    have hp : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hsk : s = (k : ℂ) := by
      have : ↑Real.pi * s = ↑Real.pi * (k : ℂ) := by
        rw [hk]
        ring
      exact mul_left_cancel₀ hp this
    exact hs ⟨k, hsk.symm⟩
  -- 组合: 4·(2π)^{-1}·(π/sin πs)·((1/2)sin πs) = 1
  rw [h1, hpow, hgamma, hsin]
  rw [cpow_neg_one]
  field_simp [hsne]
  ring

/-- **χ 沿临界线模恒 1**: |χ(1/2+it)| = 1。
    χ(1/2+it)·χ(1/2-it) = χ(s)·χ(1-s) = 1 且 χ(1/2-it) = conj χ(1/2+it)
    (共轭对称) ⟹ |χ|² = 1。χ 的相位场 (连续) 是单位圆路径。 -/
theorem chi_modulus_one (t : ℝ) : ‖chi (1 / 2 + (t : ℂ) * Complex.I)‖ = 1 := by
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  -- conj χ(s) = χ(conj s) = χ(1-s) (s = 1/2+it ⟹ conj s = 1-s)
  have hconj : conj (chi s) = chi (1 - s) := by
    have hs : conj s = 1 - s := by
      dsimp [s]
      apply Complex.ext
      · simp
        norm_num
      · simp
    rw [← chi_conj s, hs]
  -- s ∉ ℤ (临界线上非整数)
  have hnot : s ∉ Set.range (fun n : ℤ => (n : ℂ)) := by
    intro h
    rcases h with ⟨n, hn⟩
    -- 虚部: n 的虚部 0 = t ⟹ t = 0 ⟹ s = 1/2
    have htim : (n : ℂ).im = t := by
      have hc := congrArg (fun z : ℂ => z.im) hn
      calc (n : ℂ).im = s.im := hc
        _ = t := by dsimp [s]; simp
    have ht0 : t = 0 := by
      rw [← htim]
      simp
    -- s = 1/2 ⟹ (n : ℂ) = 1/2
    have hs2 : s = 1 / 2 := by
      dsimp [s]
      rw [ht0]
      simp
    have hn2 : (n : ℂ) = (1 / 2 : ℂ) := by
      calc (n : ℂ) = s := hn
        _ = 1 / 2 := hs2
    -- 实部: n = 1/2 (ℝ), 与整数矛盾 (2n = 1)
    have hnn : (n : ℝ) = 1 / 2 := by
      have hc := congrArg (fun z : ℂ => z.re) hn2
      have hre2 : (n : ℂ).re = 1 / 2 := by simpa using hc
      have hnri : (n : ℂ).re = (n : ℝ) := Complex.ofReal_re (n : ℝ)
      rw [← hnri, hre2]
    have h2 : (2 : ℝ) * (n : ℝ) = 1 := by
      rw [hnn]
      norm_num
    have h2z : (2 * n : ℤ) = 1 := by
      exact_mod_cast h2
    omega
  -- χ(s)·χ(1-s) = 1
  have hmul : chi s * chi (1 - s) = 1 := chi_mul_chi_one_sub hnot
  -- ‖χ(s)‖² = χ(s)·conj χ(s)
  have hsq : ‖chi s‖ ^ 2 = (chi s * conj (chi s)).re := by
    rw [Complex.sq_norm]
    unfold Complex.normSq
    simp [mul_re, conj_re, conj_im]
  -- ‖χ(s)‖² = 1
  have hsq1 : ‖chi s‖ ^ 2 = 1 := by
    rw [hsq, hconj, hmul]
    simp
  -- ‖χ(s)‖ ≥ 0, 平方为 1 ⟹ = 1
  have hnonneg : 0 ≤ ‖chi s‖ := norm_nonneg _
  change ‖chi s‖ = 1
  have hsq1' : ‖chi s‖ ^ 2 = (1 : ℝ) ^ 2 := by
    simpa [one_pow] using hsq1
  exact (sq_eq_sq₀ hnonneg (by norm_num : (0 : ℝ) ≤ 1)).mp hsq1'

/-- **θ_χ(T) = arg χ(1/2+iT) (主枝)**: χ 沿临界线的显式相位。 -/
def thetaChi (T : ℝ) : ℝ :=
  (Complex.log (chi (1 / 2 + (T : ℂ) * Complex.I))).im

/-- χ 圈数 (主枝): 相位/2π。 -/
def chiTurnNumber (T : ℝ) : ℝ :=
  thetaChi T / (2 * ↑Real.pi)


/-- **log cosh 分解**: log cosh(x) = x - log 2 + log(1+e^{-2x}) (x ≥ 0)。
    cosh x = e^x·(1+e^{-2x})/2 (提取 e^x), log 展开。 -/
theorem log_cosh_self_add (x : ℝ) (_hx : 0 ≤ x) :
    Real.log (Real.cosh x) = x - Real.log 2 + Real.log (1 + Real.exp (-2 * x)) := by
  -- cosh x = (e^x + e^{-x})/2 = e^x·(1+e^{-2x})/2
  have hcosh : Real.cosh x = Real.exp x * (1 + Real.exp (-2 * x)) / 2 := by
    rw [Real.cosh_eq]
    -- e^x + e^{-x} = e^x·(1 + e^{-2x}): 提取 e^x
    have hx1 : Real.exp x + Real.exp (-x) = Real.exp x * (1 + Real.exp (-2 * x)) := by
      -- e^{-x} = e^x·e^{-2x} (exp_add: e^{x + (-2x)} = e^{-x})
      have he : Real.exp (-x) = Real.exp x * Real.exp (-2 * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    rw [hx1]
  -- log 展开: log(e^x·A/2) = log(e^x) + log A - log 2
  have he : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hA : 0 < 1 + Real.exp (-2 * x) := by positivity
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [hcosh]
  rw [Real.log_div (ne_of_gt (mul_pos he hA)) (ne_of_gt h2)]
  rw [Real.log_mul (ne_of_gt he) (ne_of_gt hA)]
  rw [Real.log_exp]
  -- x + log A - log 2 整理
  ring

/-- **|Γ(1/2+it)|² 精确公式** (反射公式): |Γ(1/2+it)|² = π/cosh(πt)。
    Γ(s)Γ(1-s) = π/sin(πs) (反射) + sin(π/2+iπt) = cos(iπt) = cosh(πt)
    + Γ 实系数共轭 (|Γ|² = Γ·conj Γ = Γ(s)·Γ(1-s))。 -/
theorem gammaSq_half_line (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  -- |Γ(s)|² = Γ(s)·conj Γ(s) = Γ(s)·Γ(1-s) (Γ 实系数, conj s = 1-s)
  have hsq : ‖Complex.Gamma s‖ ^ 2 = (Complex.Gamma s * Complex.Gamma (1 - s)).re := by
    -- |z|² = (z·conj z).re
    have hnorm : ‖Complex.Gamma s‖ ^ 2 = (Complex.Gamma s * conj (Complex.Gamma s)).re := by
      rw [Complex.sq_norm]
      unfold Complex.normSq
      simp [mul_re, conj_re, conj_im]
    -- conj (Γ s) = Γ (1-s) (Gamma_conj + conj s = 1-s)
    have hconj : conj (Complex.Gamma s) = Complex.Gamma (1 - s) := by
      have hcs : conj s = 1 - s := by
        dsimp [s]
        apply Complex.ext
        · simp
          norm_num
        · simp
      simpa [hcs] using (Gamma_conj s).symm
    -- (Γs·Γ(1-s)).re = (Γs·conj Γs).re
    have hright : (Complex.Gamma s * Complex.Gamma (1 - s)).re =
        (Complex.Gamma s * conj (Complex.Gamma s)).re := by
      exact congrArg (fun w : ℂ => (Complex.Gamma s * w).re) hconj.symm
    exact hnorm.trans hright.symm
  -- 反射: Γ(s)·Γ(1-s) = π/sin(πs)
  have href : Complex.Gamma s * Complex.Gamma (1 - s) = Real.pi / Complex.sin (Real.pi * s) := by
    simpa [mul_comm] using (Gamma_mul_Gamma_one_sub s)
  -- sin(πs) = sin(π/2 + iπt) = cos(iπt) = cosh(πt) (实数)
  have hsin : Complex.sin (Real.pi * s) = (Real.cosh (Real.pi * t) : ℂ) := by
    -- π·s = π/2 + i·(πt): 展开
    have harg : Real.pi * s = Real.pi / 2 + (Real.pi * t : ℂ) * Complex.I := by
      dsimp [s]
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg]
    -- sin(π/2 + z) = cos z (交换序); cos(i·(πt)) = cosh(πt)
    rw [show ↑Real.pi / 2 + ↑Real.pi * ↑t * I = ↑Real.pi * ↑t * I + ↑Real.pi / 2 by ring]
    rw [Complex.sin_add_pi_div_two]
    rw [Complex.cos_mul_I]
    -- cosh 的 ℝ → ℂ cast: (cosh (πt) : ℂ) = Complex.cosh (πt : ℂ)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh (Real.pi * t)]
  -- 组合: |Γ|² = π/cosh(πt) (实数, sin 实数)
  have hsq1 : ‖Complex.Gamma s‖ ^ 2 = (Real.pi / Real.cosh (Real.pi * t) : ℝ) := by
    -- 从 hsq/href/hsin
    rw [hsq, href]
    rw [hsin]
    -- ↑π/↑(cosh πt) = ↑(π/cosh πt), 实部 = π/cosh πt (ofReal_div 反向 + ofReal_re)
    rw [← Complex.ofReal_div]
    rw [Complex.ofReal_re]
  -- 展开 s
  simpa [s] using hsq1

/-- **log|Γ(1/2+it)| 精确公式**: log|Γ(1/2+it)| = (1/2)(log π - log cosh(πt))。
    由 |Γ|² = π/cosh(πt) (gammaSq_half_line) + log_sqrt。 -/
theorem logAbsGamma_half_line (t : ℝ) :
    Real.log ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      (1 / 2) * (Real.log Real.pi - Real.log (Real.cosh (Real.pi * t))) := by
  -- |Γ|² = π/cosh(πt) > 0, log|Γ| = (1/2)log|Γ|²
  have hsq := gammaSq_half_line t
  have hpos : 0 < Real.pi / Real.cosh (Real.pi * t) := by
    exact div_pos Real.pi_pos (Real.cosh_pos _)
  -- log‖Γ‖ = log √‖Γ‖² = (1/2)log‖Γ‖²
  have hsq2 : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := hsq
  have hsqrt : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) := by
    -- ‖Γ‖ ≥ 0 且 ‖Γ‖² = (√x)² ⟹ ‖Γ‖ = √x
    have hnonneg : 0 ≤ ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
    have hsq3 : ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
        (Real.sqrt (Real.pi / Real.cosh (Real.pi * t))) ^ 2 := by
      rw [hsq2, Real.sq_sqrt (le_of_lt hpos)]
    exact (sq_eq_sq₀ (a := ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖)
      (b := Real.sqrt (Real.pi / Real.cosh (Real.pi * t))) hnonneg (Real.sqrt_nonneg _)).mp hsq3
  rw [hsqrt, Real.log_sqrt (le_of_lt hpos)]
  -- (1/2)log(π/cosh) = (1/2)(log π - log cosh)
  rw [Real.log_div (ne_of_gt Real.pi_pos) (ne_of_gt (Real.cosh_pos _))]
  ring

/-- **log|Γ(1/2+it)| 渐近主项** (t ≥ 0):
    log|Γ(1/2+it)| = (1/2)log(2π) - πt/2 - (1/2)log(1+e^{-2πt})。
    由精确公式 + log cosh 分解; 误差项 -log(1+e^{-2πt}) 指数衰减。 -/
theorem logAbsGamma_half_line_asymp (t : ℝ) (ht : 0 ≤ t) :
    Real.log ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      (1 / 2) * (Real.log (2 * Real.pi)) - (Real.pi * t) / 2 -
        (1 / 2) * Real.log (1 + Real.exp (-2 * Real.pi * t)) := by
  rw [logAbsGamma_half_line]
  rw [log_cosh_self_add (Real.pi * t) (mul_nonneg (le_of_lt Real.pi_pos) ht)]
  -- (1/2)(log π - (x - log 2 + log A)) = (1/2)log(2π) - x/2 - (1/2)log A
  have hlog : Real.log Real.pi + Real.log 2 = Real.log (Real.pi * 2) := by
    rw [Real.log_mul (ne_of_gt Real.pi_pos) (by norm_num : (2 : ℝ) ≠ 0)]
  -- 左侧整理: (1/2)(log π - x + log 2 - log A) = (1/2)(log π + log 2) - x/2 - (1/2)log A
  rw [show (1 / 2 : ℝ) * (Real.log Real.pi - (Real.pi * t - Real.log 2 +
        Real.log (1 + Real.exp (-2 * (Real.pi * t))))) =
      (1 / 2 : ℝ) * (Real.log Real.pi + Real.log 2) - (Real.pi * t) / 2 -
        (1 / 2) * Real.log (1 + Real.exp (-2 * (Real.pi * t))) by ring]
  rw [hlog]
  ring

-- ============================================================
-- T6j: Stirling 第二层 — sin 相位精确项 + e^{iθ_χ} = χ 桥 (2026-08-19)
-- 渐进用桥解决 (用户方法论): 不造 Binet 轮子, 桥 = 显式相位刻度
--   e^{iθ_χ(T)} = χ(1/2+iT)  (与 e^{iπS} = u 平行: χ 的 e^{iπ} 桥)
--   Im log sin(π/4+iπT/2) = arctan(tanh(πT/2)) → π/4 (显式相位, 精确渐近)
-- θ_χ 的 Backlund 主项 (T/2)log(T/2π) - T/2 - π/8 + O(1/T) 是经典 KNOWN
-- (Binet 展开, 标注引用, 不重新证明); 本文件给出可完全证明的桥接结构。
-- ============================================================

/-- **e^{iθ_χ} = χ 桥**: θ_χ 的 e^{iπ} 次幂 = χ 自身。
    |χ(1/2+iT)| = 1 ⟹ log χ 纯虚 ⟹ log χ = i·θ_χ ⟹ e^{log χ} = e^{iθ_χ} = χ。
    与 e^{iπS(T)} = u(T) 平行: u 是 ζ 的隐式相位, χ 是显式相位 (快路径)。 -/
theorem exp_thetaChi_eq_chi (T : ℝ) :
    Complex.exp ((thetaChi T : ℂ) * Complex.I) =
      chi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) := by
  -- log χ = i·θ_χ: 实部 = log|χ| = log 1 = 0, 虚部 = θ_χ (定义)
  have hlog : Complex.log (chi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)) =
      (thetaChi T : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.log_re, chi_modulus_one, Real.log_one]
      simp [thetaChi]
    · simp [thetaChi]
  -- e^{log χ} = χ (χ ≠ 0, |χ| = 1)
  have hne : chi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hnorm : ‖chi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ = 0 := by
      rw [h]
      simp
    rw [chi_modulus_one T] at hnorm
    norm_num at hnorm
  rw [← hlog]
  exact Complex.exp_log hne

/-- **sin 相位精确**: Im log sin(π/4+iπT/2) = arctan(tanh(πT/2))。
    sin(π/4+iy) = sin(π/4)cos(iy) + cos(π/4)sin(iy) = (√2/2)(cosh y + i·sinh y),
    arg = arctan(sinh y/cosh y) = arctan(tanh y) (re > 0 ⟹ arg ∈ (-π/2, π/2))。 -/
theorem sin_phase_exact (T : ℝ) :
    (Complex.log (Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2))).im
      = Real.arctan (Real.tanh (Real.pi * T / 2)) := by
  let y : ℝ := Real.pi * T / 2
  -- sin(π/4 + iy) = (√2/2)(cosh y + i·sinh y)
  have hsin : Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2) =
      (↑(Real.sqrt 2 / 2) : ℂ) * (↑(Real.cosh y) + ↑(Real.sinh y) * Complex.I) := by
    have harg : ↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2 =
        (↑Real.pi / 4 : ℂ) + (y : ℂ) * Complex.I := by
      dsimp [y]
      apply Complex.ext
      · simp
        ring
      · simp
    rw [harg]
    rw [Complex.sin_add]
    have hsinp : Complex.sin (↑Real.pi / 4) = ↑(Real.sqrt 2 / 2) := by
      calc
        Complex.sin (↑Real.pi / 4) = Complex.sin (↑(Real.pi / 4)) := by
          congr 1
          rw [Complex.ofReal_div]
          norm_num
        _ = ↑(Real.sin (Real.pi / 4)) := by rw [Complex.ofReal_sin]
        _ = ↑(Real.sqrt 2 / 2) := by rw [Real.sin_pi_div_four]
    have hcosp : Complex.cos (↑Real.pi / 4) = ↑(Real.sqrt 2 / 2) := by
      calc
        Complex.cos (↑Real.pi / 4) = Complex.cos (↑(Real.pi / 4)) := by
          congr 1
          rw [Complex.ofReal_div]
          norm_num
        _ = ↑(Real.cos (Real.pi / 4)) := by rw [Complex.ofReal_cos]
        _ = ↑(Real.sqrt 2 / 2) := by rw [Real.cos_pi_div_four]
    have hcosi : Complex.cos ((y : ℂ) * Complex.I) = ↑(Real.cosh y) := by
      rw [Complex.cos_mul_I]
      rw [← Complex.ofReal_cosh]
    have hsini : Complex.sin ((y : ℂ) * Complex.I) = ↑(Real.sinh y) * Complex.I := by
      rw [Complex.sin_mul_I]
      rw [← Complex.ofReal_sinh]
    rw [hsinp, hcosp, hcosi, hsini]
    ring
  -- arg: z = (√2/2)(cosh y + i·sinh y), re > 0 ⟹ arg = arctan(tanh y)
  have hre : 0 < (↑(Real.cosh y) : ℂ).re := by simp [Real.cosh_pos]
  have hz : (↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I ≠ 0 := by
    intro h
    have : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).re = 0 := by rw [h]; simp
    simp at this
    linarith [Real.cosh_pos y]
  have harg' : (Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2)).arg
      = Real.arctan (Real.tanh y) := by
    rw [hsin]
    -- arg(↑(√2/2)·z) = arg z (正标量, arg_real_mul)
    have hpos : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
    have hscalar : ((↑(Real.sqrt 2 / 2) : ℂ) * ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I)).arg
        = ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg := by
      simpa using
        (Complex.arg_real_mul ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I) hpos)
    rw [hscalar]
    -- tan(arg z) = sinh/cosh = tanh y (tan_arg), arg ∈ (-π/2, π/2) (re > 0)
    have htan : Real.tan (((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg)
        = Real.tanh y := by
      have hre_z : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).re = Real.cosh y := by
        simp only [add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
        ring
      have him_z : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).im = Real.sinh y := by
        simp only [add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re]
        simp
      rw [Complex.tan_arg]
      rw [hre_z, him_z]
      rw [Real.tanh_eq_sinh_div_cosh]
    have hmem : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg
        ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      -- cos(arg z) = re/‖z‖ > 0 且 arg ∈ (-π, π] ⟹ |arg| < π/2
      have hcos : 0 < Real.cos (((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) := by
        rw [Complex.cos_arg hz]
        -- re/‖z‖ > 0
        have hre' : 0 < ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).re := by
          simp [Real.cosh_pos y]
        exact div_pos hre' (norm_pos_iff.mpr hz)
      have hargmem := Complex.arg_mem_Ioc ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I)
      constructor
      · by_contra hnot
        have hle : ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg ≤ -(Real.pi / 2) := by
          linarith
        have hcosle : Real.cos (((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) ≤ 0 := by
          have h1 : Real.pi / 2 ≤ -(((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) := by
            linarith
          have h2 : -(((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) ≤
              Real.pi + Real.pi / 2 := by
            have hlt : -(((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) < Real.pi := by
              linarith [hargmem.1]
            linarith
          have hc : Real.cos (-(((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg)) ≤ 0 := by
            exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
          rwa [Real.cos_neg] at hc
        linarith
      · by_contra hnot
        have hle : Real.pi / 2 ≤ ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg := by
          linarith
        have hcosle : Real.cos (((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg) ≤ 0 := by
          exact Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith [hargmem.2])
        linarith
    -- arctan(tan(arg)) = arg (arg ∈ (-π/2, π/2)), tan(arg) = tanh y
    have harct : Real.arctan (Real.tanh y) = ((↑(Real.cosh y) : ℂ) + ↑(Real.sinh y) * Complex.I).arg := by
      rw [← htan]
      exact Real.arctan_tan hmem.1 hmem.2
    exact harct.symm
  -- Im log = arg (log_im)
  rw [Complex.log_im]
  -- y = πT/2 代入
  simpa [y] using harg'

/-- **sin 相位渐近**: Im log sin(π/4+iπT/2) → π/4 (T → ∞)。
    arctan(tanh(πT/2)) → arctan 1 = π/4: tanh → 1 (指数表示) + arctan 连续。 -/
theorem sin_phase_tendsto_pi_div_four :
    Tendsto (fun T : ℝ => (Complex.log
        (Complex.sin (↑Real.pi * ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) / 2))).im)
      atTop (𝓝 (Real.pi / 4)) := by
  -- tanh x → 1: tanh x = (e^{2x}-1)/(e^{2x}+1) = 1 - 2/(e^{2x}+1)
  have htanh : Tendsto Real.tanh atTop (𝓝 1) := by
    have hdecomp : ∀ x : ℝ, Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
      intro x
      calc
        Real.tanh x = (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) := by
          rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
          field_simp
        _ = 1 - 2 * (Real.exp (-x) / (Real.exp x + Real.exp (-x))) := by
          field_simp
          ring
        _ = 1 - 2 / (Real.exp (2 * x) + 1) := by
          congr 1
          -- e^{-x}/(e^x+e^{-x}) = 1/(e^{2x}+1): 交叉乘 (field_simp)
          field_simp [Real.exp_ne_zero]
          -- e^{-x}·(e^{2x}+1) = e^{-x}·e^{2x} + e^{-x} = e^{x} + e^{-x}
          rw [mul_add]
          rw [← Real.exp_add]
          have hpar : -x + 2 * x = x := by ring
          rw [hpar]
          simp
    have h_exp : Tendsto (fun x : ℝ => Real.exp (2 * x)) atTop atTop := by
      exact Real.tendsto_exp_atTop.comp
        (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id)
    have h_inv : Tendsto (fun x : ℝ => (Real.exp (2 * x) + 1)⁻¹) atTop (𝓝 0) := by
      have h_add : Tendsto (fun x : ℝ => Real.exp (2 * x) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 h_exp
      exact tendsto_inv_atTop_zero.comp h_add
    have h_two : Tendsto (fun x : ℝ => 2 * (Real.exp (2 * x) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [mul_comm] using (tendsto_const_nhds.mul h_inv)
    have h_one : Tendsto (fun x : ℝ => 1 - 2 * (Real.exp (2 * x) + 1)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h_two
    simpa [hdecomp] using (h_one.congr' (Eventually.of_forall (fun x => by rw [hdecomp x]; ring)))
  -- arctan 连续 + tanh(πT/2) → 1 + arctan 1 = π/4
  have htan' : Tendsto (fun T : ℝ => Real.tanh (Real.pi * T / 2)) atTop (𝓝 1) := by
    have hmul : Tendsto (fun T : ℝ => Real.pi * T / 2) atTop atTop := by
      have hc : Tendsto (fun T : ℝ => Real.pi * T) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < Real.pi) tendsto_id
      simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
        (hc.atTop_div_const (by positivity : (0 : ℝ) < 2))
    exact htanh.comp hmul
  have harct : Tendsto (fun T : ℝ => Real.arctan (Real.tanh (Real.pi * T / 2))) atTop
      (𝓝 (Real.pi / 4)) := by
    have hc : ContinuousAt Real.arctan 1 := Real.continuousAt_arctan
    simpa [Function.comp_def, Real.arctan_one] using (hc.tendsto.comp htan')
  -- sin_phase_exact 代入
  refine harct.congr' (Eventually.of_forall (fun T => ?_))
  rw [← sin_phase_exact]



/-- 每项 n^{-s} 在临界线的显式相位: n^{-(1/2+it)} = n^{-1/2}·(cos(t·ln n) - i·sin(t·ln n))。
    "1 2 3 4 各有各的相位": 频率 ln n, 模 n^{-1/2}, 相位 -t·ln n (线性)。 -/
theorem term_on_line_explicit (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I) : ℂ)
      = (Real.exp (-Real.log n / 2) : ℂ) * (Real.cos (t * Real.log n) : ℂ)
        - (Real.exp (-Real.log n / 2) : ℂ) * (Real.sin (t * Real.log n) : ℂ) * Complex.I := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog]
  have hdecomp : (Real.log n : ℂ) * (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))
      = ((-Real.log n / 2 : ℝ) : ℂ) + ((-(t * Real.log n) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im] <;> ring
  rw [hdecomp, Complex.exp_add, ← Complex.ofReal_exp]
  -- exp((-(t·ln n))·I) = cos(t·ln n) - i·sin(t·ln n)
  rw [Complex.exp_mul_I]
  simp
  ring


/-- u(s) = ζ(s)/|ζ(s)|: 单位圆投影 (相位)。 -/
def zetaUnit (s : ℂ) : ℂ := riemannZeta s / ‖riemannZeta s‖

/-- u 在 ζ ≠ 0 且 s ≠ 1 处连续: ζ 在 {1}ᶜ 可微, 除法分母非零。 -/
lemma continuousOn_zetaUnit :
    ContinuousOn zetaUnit ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) := by
  have hzeta : ContinuousOn riemannZeta ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) :=
    differentiableOn_riemannZeta.continuousOn.mono (by intro s hs; exact hs.1)
  have hnorm : ContinuousOn (fun s : ℂ => (‖riemannZeta s‖ : ℂ))
      ({1}ᶜ ∩ {s | riemannZeta s ≠ 0}) := by
    intro x hx
    exact ContinuousWithinAt.comp (t := Set.univ) continuous_ofReal.continuousWithinAt
      (hzeta x hx).norm (by intro y hy; simp)
  refine hzeta.div hnorm ?_
  intro s hs
  exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hs.2)


-- arg(2π) ≠ π (conj_cpow 的条件: 底数不在负实轴)

theorem zeta_local_expansion (s₀ : ℂ) (hs₀ : s₀ ≠ 1) (_hz₀ : riemannZeta s₀ = 0) :
    ∃ m : ℕ, ∃ g : ℂ → ℂ,
      (∀ᶠ s in 𝓝 s₀, riemannZeta s = (s - s₀) ^ m * g s) ∧
        g s₀ ≠ 0 ∧ ContinuousAt g s₀ := by
  -- ζ 在 s₀ 解析 (s₀ ≠ 1): analyticOn_riemannZeta 已是 AnalyticOnNhd
  have hana : AnalyticAt ℂ riemannZeta s₀ :=
    (analyticOn_riemannZeta.analyticOn).analyticAt
      (isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_singleton_iff] using hs₀))
  rcases hana with ⟨p, hp⟩
  -- p ≠ 0: ζ 在 s₀ 不恒零 (若恒零, 由解析延拓 ζ 在 {1}ᶜ 全零, 与 ζ(2) ≠ 0 矛盾)
  have hp_ne : p ≠ 0 := by
    intro hp0
    have hzero : ∀ᶠ z in 𝓝 s₀, riemannZeta z = 0 := hp.locally_zero_iff.mpr hp0
    have hfreq : ∃ᶠ z in 𝓝[≠] s₀, riemannZeta z = 0 :=
      (hzero.filter_mono nhdsWithin_le_nhds).frequently
    have heq : EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
      analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
        (by simpa [Set.mem_compl_singleton_iff] using hs₀) hfreq
    have hz2 : riemannZeta 2 = 0 := heq (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
    exact (riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat) hz2
  -- m = p.order, g = dslope 迭代: 展开 + 非零 + 连续
  refine ⟨p.order, (swap dslope s₀)^[p.order] riemannZeta, ?_, ?_, ?_⟩
  · -- ζ(s) = (s-s₀)^m · g(s) 逐点 (邻域内恒成立)
    exact Eventually.of_forall (fun s => by
      simpa [smul_eq_mul] using hp.eq_pow_order_mul_iterate_dslope s)
  · exact hp.iterate_dslope_fslope_ne_zero hp_ne
  · -- g 在 s₀ 连续: dslope 迭代保持解析
    exact (hp.has_fpower_series_iterate_dslope_fslope p.order).continuousAt

/-- 展开在临界线上的形式: ζ(z(t)) = (t-t₀)^m·(i^m·g(z(t)))
    (沿 t > t₀ 侧; 由 s₀ = z(t₀) 与 z(t)-s₀ = (t-t₀)·i 代入展开)。 -/
lemma zetaLine_expansion_right {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s) :
    ∀ᶠ t in 𝓝[>] t₀,
      riemannZeta (zetaLine t) = (t - t₀) ^ m * (I ^ m * g (zetaLine t)) := by
  -- 从 𝓝 s₀ 限制到 t 侧: z 连续 ⟹ preimage ∈ 𝓝 t₀; 再与 {t > t₀} 相交
  have hcont : ContinuousAt zetaLine t₀ := by
    unfold zetaLine
    fun_prop
  have hpre : ∀ᶠ t in 𝓝 t₀,
      riemannZeta (zetaLine t) = (zetaLine t - zetaLine t₀) ^ m * g (zetaLine t) :=
    ContinuousAt.preimage_mem_nhds hcont h_exp
  filter_upwards [hpre.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hgt
  -- 代数: z(t) - z(t₀) = (t - t₀)·i ⟹ (z(t)-z(t₀))^m = (t-t₀)^m · i^m
  have hdiff : zetaLine t - zetaLine t₀ = (t - t₀ : ℂ) * I := by
    unfold zetaLine
    ring_nf
  rw [ht, hdiff, mul_pow]
  ring

/-- **u 在零点右侧的极限**: u(t) → i^m·g(s₀)/|g(s₀)| (t → t₀⁺)。
    方向由 i^m 决定 (i 的迭代): 翻转向量 = m 次旋转 90°。 -/
theorem zetaUnitOnLine_tendsto_right {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    Tendsto zetaUnitOnLine (𝓝[>] t₀)
      (𝓝 (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))) := by
  -- g(z(t)) → g(s₀) 且附近非零
  have hz_cont : ContinuousAt zetaLine t₀ := by
    unfold zetaLine
    fun_prop
  have hgz_tendsto : Tendsto (fun t : ℝ => g (zetaLine t)) (𝓝[>] t₀) (𝓝 (g (zetaLine t₀))) :=
    (hg_cont.comp hz_cont).tendsto.mono_left nhdsWithin_le_nhds
  have hgz_ne : ∀ᶠ t in 𝓝[>] t₀, g (zetaLine t) ≠ 0 := by
    have hg_ne_nhds : ∀ᶠ s in 𝓝 (zetaLine t₀), g s ≠ 0 := hg_cont.eventually_ne hg
    have hgz_ne0 : ∀ᶠ t in 𝓝 t₀, g (zetaLine t) ≠ 0 :=
      ContinuousAt.preimage_mem_nhds hz_cont hg_ne_nhds
    exact hgz_ne0.filter_mono nhdsWithin_le_nhds
  -- ζ(z(t)) 的展开与模分解 (t > t₀: |t-t₀| = t-t₀, |i^m| = 1)
  have hzeta : ∀ᶠ t in 𝓝[>] t₀,
      riemannZeta (zetaLine t) = (t - t₀) ^ m * (I ^ m * g (zetaLine t)) :=
    zetaLine_expansion_right h_exp
  have hnorm : ∀ᶠ t in 𝓝[>] t₀,
      ‖riemannZeta (zetaLine t)‖ = (t - t₀) ^ m * ‖g (zetaLine t)‖ := by
    filter_upwards [hzeta, self_mem_nhdsWithin] with t ht hgt
    rw [ht, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow]
    -- ‖(t-t₀ : ℂ)‖ = |t-t₀| = t-t₀ (t > t₀)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hgt))]
    ring
  -- u(t) = i^m·g(z(t))/|g(z(t))| (消去 (t-t₀)^m)
  have hu : ∀ᶠ t in 𝓝[>] t₀,
      zetaUnitOnLine t = I ^ m * (g (zetaLine t) / ‖g (zetaLine t)‖) := by
    filter_upwards [hzeta, hnorm, hgz_ne, self_mem_nhdsWithin] with t ht hnm hgne hgt
    unfold zetaUnitOnLine
    rw [hnm, ht]
    have htne : (t - t₀ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      intro h
      exact (sub_ne_zero.mpr (ne_of_gt hgt)) (Complex.ofReal_eq_zero.mp h)
    have htnz : (t - t₀ : ℂ) ^ m ≠ 0 := pow_ne_zero m htne
    have hnnz : ‖g (zetaLine t)‖ ≠ 0 := norm_ne_zero_iff.mpr hgne
    field_simp [htnz, hnnz]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  -- 极限: i^m · (g/|g| 的极限)
  have hg_ratio : Tendsto (fun t : ℝ => g (zetaLine t) / ‖g (zetaLine t)‖)
      (𝓝[>] t₀) (𝓝 (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
    have hnz : (‖g (zetaLine t₀)‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
    have hden : Tendsto (fun t : ℝ => (‖g (zetaLine t)‖ : ℂ))
        (𝓝[>] t₀) (𝓝 ((‖g (zetaLine t₀)‖ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto (‖g (zetaLine t₀)‖)).comp hgz_tendsto.norm
    exact hgz_tendsto.div hden hnz
  exact (tendsto_const_nhds.mul hg_ratio).congr' (EventuallyEq.symm hu)

/-- **u 在零点左侧的极限**: u(t) → (-i)^m·g(s₀)/|g(s₀)| (t → t₀⁻)。
    左侧多出 (-1)^m: m 奇时反向 (翻转), m 偶时同向 (通过)。 -/
theorem zetaUnitOnLine_tendsto_left {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    Tendsto zetaUnitOnLine (𝓝[<] t₀)
      (𝓝 ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))) := by
  -- g(z(t)) → g(s₀) 且附近非零
  have hz_cont : ContinuousAt zetaLine t₀ := by
    unfold zetaLine
    fun_prop
  have hgz_tendsto : Tendsto (fun t : ℝ => g (zetaLine t)) (𝓝[<] t₀) (𝓝 (g (zetaLine t₀))) :=
    (hg_cont.comp hz_cont).tendsto.mono_left nhdsWithin_le_nhds
  have hgz_ne : ∀ᶠ t in 𝓝[<] t₀, g (zetaLine t) ≠ 0 := by
    have hg_ne_nhds : ∀ᶠ s in 𝓝 (zetaLine t₀), g s ≠ 0 := hg_cont.eventually_ne hg
    have hgz_ne0 : ∀ᶠ t in 𝓝 t₀, g (zetaLine t) ≠ 0 :=
      ContinuousAt.preimage_mem_nhds hz_cont hg_ne_nhds
    exact hgz_ne0.filter_mono nhdsWithin_le_nhds
  -- 展开 (左侧同样成立) 与模分解 (t < t₀: |t-t₀| = t₀-t)
  have hzeta : ∀ᶠ t in 𝓝[<] t₀,
      riemannZeta (zetaLine t) = (t - t₀) ^ m * (I ^ m * g (zetaLine t)) := by
    have htmp : ∀ᶠ t in 𝓝 t₀,
        riemannZeta (zetaLine t) = (zetaLine t - zetaLine t₀) ^ m * g (zetaLine t) :=
      ContinuousAt.preimage_mem_nhds hz_cont h_exp
    filter_upwards [htmp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hgt
    have hdiff : zetaLine t - zetaLine t₀ = (t - t₀ : ℂ) * I := by
      unfold zetaLine
      ring_nf
    rw [ht, hdiff, mul_pow]
    ring
  have hnorm : ∀ᶠ t in 𝓝[<] t₀,
      ‖riemannZeta (zetaLine t)‖ = (t₀ - t) ^ m * ‖g (zetaLine t)‖ := by
    filter_upwards [hzeta, self_mem_nhdsWithin] with t ht hgt
    rw [ht, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hgt))]
    ring
  -- u(t) = (t₀-t)^m·i^m·g / ((t₀-t)^m·|g|) = i^m·g/|g|: (t-t₀)^m = (-1)^m·(t₀-t)^m
  have hu : ∀ᶠ t in 𝓝[<] t₀,
      zetaUnitOnLine t = (-I) ^ m * (g (zetaLine t) / ‖g (zetaLine t)‖) := by
    filter_upwards [hzeta, hnorm, hgz_ne, self_mem_nhdsWithin] with t ht hnm hgne hgt
    unfold zetaUnitOnLine
    rw [hnm, ht]
    have hlt : t < t₀ := by simpa using hgt
    have htne : (t₀ - t : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (sub_pos.mpr hlt))
    have htnz : (t₀ - t : ℂ) ^ m ≠ 0 := pow_ne_zero m htne
    have hnnz : ‖g (zetaLine t)‖ ≠ 0 := norm_ne_zero_iff.mpr hgne
    -- (t-t₀)^m = (-1)^m·(t₀-t)^m: 从 t-t₀ = -(t₀-t)
    have hneg : (t - t₀ : ℂ) ^ m = (-1 : ℂ) ^ m * (t₀ - t) ^ m := by
      have hsub : (t - t₀ : ℂ) = -(t₀ - t : ℂ) := by ring
      calc (t - t₀ : ℂ) ^ m = (-(t₀ - t : ℂ)) ^ m := by rw [hsub]
        _ = (-1 : ℂ) ^ m * (t₀ - t) ^ m := by
          have hnegmul : -(t₀ - t : ℂ) = (-1 : ℂ) * (t₀ - t : ℂ) := by ring
          rw [hnegmul, mul_pow]
    -- i^m · (-1)^m = (-i)^m (及交换序版本)
    have hIm : I ^ m * (-1 : ℂ) ^ m = (-I) ^ m := by
      rw [← mul_pow]
      ring_nf
    have hIm' : (-1 : ℂ) ^ m * I ^ m = (-I) ^ m := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hIm
    rw [hneg]
    field_simp [htnz, hnnz]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow]
    -- 左侧重排使 (-1)^m·I^m 相邻, 用 hIm' 合并为 (-I)^m
    rw [show (-1 : ℂ) ^ m * ↑((t₀ - t) ^ m) * I ^ m * ↑‖g (zetaLine t)‖ =
        ↑((t₀ - t) ^ m) * ↑‖g (zetaLine t)‖ * ((-1 : ℂ) ^ m * I ^ m) by ring]
    rw [hIm']
    rw [← Complex.ofReal_mul]
  -- 极限
  have hg_ratio : Tendsto (fun t : ℝ => g (zetaLine t) / ‖g (zetaLine t)‖)
      (𝓝[<] t₀) (𝓝 (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
    have hnz : (‖g (zetaLine t₀)‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
    have hden : Tendsto (fun t : ℝ => (‖g (zetaLine t)‖ : ℂ))
        (𝓝[<] t₀) (𝓝 ((‖g (zetaLine t₀)‖ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto (‖g (zetaLine t₀)‖)).comp hgz_tendsto.norm
    exact hgz_tendsto.div hden hnz
  exact (tendsto_const_nhds.mul hg_ratio).congr' (EventuallyEq.symm hu)


/-- **翻转比值 (乘除法对消)**: σ(t) = 2t₀-t 是 t₀ 的反射 (右侧 ↔ 左侧),
    u(σ(t))/u(t) → (-1)^m (t → t₀⁺)。
    ζ 的展开因子 (t-t₀)^m·i^m 与模 |(t-t₀)^m| 在比值中全部对消,
    g/|g| 因子在极限中自消 (g 连续) — 只剩符号 (-1)^m。
    乘除法对消: 两个对称方向的相位贡献相消, 留 (−1)^m (共轭反射对称)。 -/
theorem flip_ratio_reflection {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    Tendsto (fun t : ℝ => zetaUnitOnLine (2 * t₀ - t) / zetaUnitOnLine t) (𝓝[>] t₀)
      (𝓝 ((-1 : ℂ) ^ m)) := by
  -- 反射的连续性: σ 与 z∘σ; z(σ t₀) = z(t₀) (2t₀-t₀ = t₀)
  have hz_cont : ContinuousAt zetaLine t₀ := by
    unfold zetaLine
    fun_prop
  have hcont : ContinuousAt (fun t : ℝ => zetaLine (2 * t₀ - t)) t₀ := by
    unfold zetaLine
    fun_prop
  have hz : zetaLine (2 * t₀ - t₀) = zetaLine t₀ := by
    unfold zetaLine
    congr 1
    ring
  -- ζ(z(σ t)) 的展开: z(σ t) - s₀ = (t₀-t)·i
  have hzeta_sigma : ∀ᶠ t in 𝓝[>] t₀,
      riemannZeta (zetaLine (2 * t₀ - t)) = (t₀ - t) ^ m * (I ^ m * g (zetaLine (2 * t₀ - t))) := by
    have h_exp' : ∀ᶠ s in 𝓝 (zetaLine (2 * t₀ - t₀)),
        riemannZeta s = (s - zetaLine t₀) ^ m * g s := by
      simpa [hz] using h_exp
    have hpre : ∀ᶠ t in 𝓝 t₀,
        riemannZeta (zetaLine (2 * t₀ - t)) =
          (zetaLine (2 * t₀ - t) - zetaLine t₀) ^ m * g (zetaLine (2 * t₀ - t)) :=
      ContinuousAt.preimage_mem_nhds hcont h_exp'
    filter_upwards [hpre.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hgt
    have hdiff : zetaLine (2 * t₀ - t) - zetaLine t₀ = (t₀ - t : ℂ) * I := by
      unfold zetaLine
      apply Complex.ext
      · simp
      · simp
        ring
    rw [ht, hdiff, mul_pow]
    ring
  -- g(z(σ t)) → g(s₀) 且附近非零
  have hgσ_tendsto : Tendsto (fun t : ℝ => g (zetaLine (2 * t₀ - t))) (𝓝[>] t₀)
      (𝓝 (g (zetaLine t₀))) := by
    have hcont' : Tendsto (fun t : ℝ => zetaLine (2 * t₀ - t)) (𝓝 t₀) (𝓝 (zetaLine t₀)) := by
      simpa [hz] using hcont.tendsto
    have ht := hg_cont.tendsto.comp hcont'
    have hg_cod : g (zetaLine (2 * t₀ - t₀)) = g (zetaLine t₀) := congrArg g hz
    simpa [Function.comp_def, hg_cod] using ht.mono_left nhdsWithin_le_nhds
  have hgσ_ne : ∀ᶠ t in 𝓝[>] t₀, g (zetaLine (2 * t₀ - t)) ≠ 0 := by
    have hne' : ∀ᶠ s in 𝓝 (zetaLine (2 * t₀ - t₀)), g s ≠ 0 := by
      simpa [hz] using hg_cont.eventually_ne hg
    have hgσ_ne0 : ∀ᶠ t in 𝓝 t₀, g (zetaLine (2 * t₀ - t)) ≠ 0 :=
      ContinuousAt.preimage_mem_nhds hcont hne'
    exact hgσ_ne0.filter_mono nhdsWithin_le_nhds
  -- u(σ t) = (-1)^m·(i^m·(g(z(σ t))/|g(z(σ t))|)): (t₀-t)^m = (-1)^m·(t-t₀)^m, |t₀-t| = t-t₀
  have hu_sigma : ∀ᶠ t in 𝓝[>] t₀,
      zetaUnitOnLine (2 * t₀ - t) =
        (-1 : ℂ) ^ m * (I ^ m * (g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖)) := by
    filter_upwards [hzeta_sigma, hgσ_ne, self_mem_nhdsWithin] with t ht hgne hgt
    unfold zetaUnitOnLine
    have hnm : ‖(t₀ - t : ℂ) ^ m * (I ^ m * g (zetaLine (2 * t₀ - t)))‖ =
        (t - t₀) ^ m * ‖g (zetaLine (2 * t₀ - t))‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hgt))]
      ring
    rw [ht, hnm]
    have htne : (t - t₀ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      intro h
      exact (sub_ne_zero.mpr (ne_of_gt hgt)) (Complex.ofReal_eq_zero.mp h)
    have htnz : (t - t₀ : ℂ) ^ m ≠ 0 := pow_ne_zero m htne
    have hnnz : ‖g (zetaLine (2 * t₀ - t))‖ ≠ 0 := norm_ne_zero_iff.mpr hgne
    -- (t₀-t)^m = (-1)^m·(t-t₀)^m
    have hneg : (t₀ - t : ℂ) ^ m = (-1 : ℂ) ^ m * (t - t₀) ^ m := by
      have hsub : (t₀ - t : ℂ) = -(t - t₀ : ℂ) := by ring
      calc (t₀ - t : ℂ) ^ m = (-(t - t₀ : ℂ)) ^ m := by rw [hsub]
        _ = (-1 : ℂ) ^ m * (t - t₀) ^ m := by
          have hnegmul : -(t - t₀ : ℂ) = (-1 : ℂ) * (t - t₀ : ℂ) := by ring
          rw [hnegmul, mul_pow]
    rw [hneg]
    field_simp [htnz, hnnz]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    -- (-1)^m·(i^m·g)·‖g‖⁻¹ = (-1)^m·(i^m·(g/‖g‖)): 乘除重排 (field_simp 已化简)
  -- u(t) = i^m·(g(z t)/|g(z t)|) (右侧, 与 zetaUnitOnLine_tendsto_right 内相同)
  have hzeta : ∀ᶠ t in 𝓝[>] t₀,
      riemannZeta (zetaLine t) = (t - t₀) ^ m * (I ^ m * g (zetaLine t)) :=
    zetaLine_expansion_right h_exp
  have hgz_ne : ∀ᶠ t in 𝓝[>] t₀, g (zetaLine t) ≠ 0 := by
    have hg_ne_nhds : ∀ᶠ s in 𝓝 (zetaLine t₀), g s ≠ 0 := hg_cont.eventually_ne hg
    have hgz_ne0 : ∀ᶠ t in 𝓝 t₀, g (zetaLine t) ≠ 0 :=
      ContinuousAt.preimage_mem_nhds hz_cont hg_ne_nhds
    exact hgz_ne0.filter_mono nhdsWithin_le_nhds
  have hu : ∀ᶠ t in 𝓝[>] t₀,
      zetaUnitOnLine t = I ^ m * (g (zetaLine t) / ‖g (zetaLine t)‖) := by
    filter_upwards [hzeta, hgz_ne, self_mem_nhdsWithin] with t ht hgne hgt
    unfold zetaUnitOnLine
    have hnm : ‖(t - t₀ : ℂ) ^ m * (I ^ m * g (zetaLine t))‖ =
        (t - t₀) ^ m * ‖g (zetaLine t)‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hgt))]
      ring
    rw [ht, hnm]
    have htne : (t - t₀ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      intro h
      exact (sub_ne_zero.mpr (ne_of_gt hgt)) (Complex.ofReal_eq_zero.mp h)
    have htnz : (t - t₀ : ℂ) ^ m ≠ 0 := pow_ne_zero m htne
    have hnnz : ‖g (zetaLine t)‖ ≠ 0 := norm_ne_zero_iff.mpr hgne
    field_simp [htnz, hnnz]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  -- 比值: i^m 因子对消 ⟹ (-1)^m·(gσ/|gσ|)/(g/|g|)
  have hratio : ∀ᶠ t in 𝓝[>] t₀,
      zetaUnitOnLine (2 * t₀ - t) / zetaUnitOnLine t =
        (-1 : ℂ) ^ m * ((g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖) /
          (g (zetaLine t) / ‖g (zetaLine t)‖)) := by
    filter_upwards [hu_sigma, hu] with t hs h
    rw [hs, h]
    field_simp [pow_ne_zero m (by norm_num : (I : ℂ) ≠ 0)]
  -- 两个 g 比值因子 → g(s₀)/|g(s₀)|, 商 → 1
  have hratio1 : Tendsto (fun t => g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖)
      (𝓝[>] t₀) (𝓝 (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
    have hnz : (‖g (zetaLine t₀)‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
    have hden : Tendsto (fun t : ℝ => (‖g (zetaLine (2 * t₀ - t))‖ : ℂ))
        (𝓝[>] t₀) (𝓝 ((‖g (zetaLine t₀)‖ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto (‖g (zetaLine t₀)‖)).comp hgσ_tendsto.norm
    exact hgσ_tendsto.div hden hnz
  have hratio2 : Tendsto (fun t => g (zetaLine t) / ‖g (zetaLine t)‖)
      (𝓝[>] t₀) (𝓝 (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
    have hgz_tendsto : Tendsto (fun t : ℝ => g (zetaLine t)) (𝓝[>] t₀) (𝓝 (g (zetaLine t₀))) :=
      (hg_cont.comp hz_cont).tendsto.mono_left nhdsWithin_le_nhds
    have hnz : (‖g (zetaLine t₀)‖ : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
    have hden : Tendsto (fun t : ℝ => (‖g (zetaLine t)‖ : ℂ))
        (𝓝[>] t₀) (𝓝 ((‖g (zetaLine t₀)‖ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto (‖g (zetaLine t₀)‖)).comp hgz_tendsto.norm
    exact hgz_tendsto.div hden hnz
  have ha : g (zetaLine t₀) / ‖g (zetaLine t₀)‖ ≠ 0 := by
    exact div_ne_zero hg (by exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg))
  have hquot : Tendsto (fun t => (g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖) /
      (g (zetaLine t) / ‖g (zetaLine t)‖)) (𝓝[>] t₀) (𝓝 1) := by
    have hq := hratio1.div hratio2 ha
    -- hq : Tendsto (f1/f2) (𝓝 (a/a)); 函数商 = 逐点商, a/a = 1
    have hfun : ((fun t => g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖) /
        (fun t => g (zetaLine t) / ‖g (zetaLine t)‖)) =
        (fun t => g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖ /
          (g (zetaLine t) / ‖g (zetaLine t)‖)) := by
      funext t
      rfl
    simpa [hfun, div_self ha] using hq
  -- 组合: (-1)^m·1 = (-1)^m
  have hmul : Tendsto (fun t : ℝ => (-1 : ℂ) ^ m *
      ((g (zetaLine (2 * t₀ - t)) / ‖g (zetaLine (2 * t₀ - t))‖) /
        (g (zetaLine t) / ‖g (zetaLine t)‖))) (𝓝[>] t₀) (𝓝 ((-1 : ℂ) ^ m)) := by
    have hc : Tendsto (fun _ : ℝ => (-1 : ℂ) ^ m) (𝓝[>] t₀) (𝓝 ((-1 : ℂ) ^ m)) :=
      tendsto_const_nhds
    simpa using hc.mul hquot
  exact hmul.congr' (EventuallyEq.symm hratio)

/-- **翻转 ⟺ 比值 = -1 (乘除法对消版)**: 由 flip_ratio_reflection,
    u(σ(t))/u(t) → (-1)^m, 翻转 (u(t₀⁻) = -u(t₀⁺)) ⟺ (-1)^m = -1 ⟺ m 奇。
    对称方向的相位 (i^m 与 (-i)^m) 在比值中对消, 留下符号 (-1)^m。 -/
theorem flip_ratio_iff_odd {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (_hg : g (zetaLine t₀) ≠ 0) (_hg_cont : ContinuousAt g (zetaLine t₀)) :
    ((-1 : ℂ) ^ m = -1) ↔ Odd m := by
  constructor
  · -- (-1)^m = -1 ⟹ m 奇: 反证 m 偶 ⟹ (-1)^m = 1
    intro h
    by_contra hm
    have heven : Even m := Nat.not_odd_iff_even.mp hm
    rcases heven with ⟨k, hk⟩
    subst m
    have hpow : (-1 : ℂ) ^ (2 * k) = 1 := by
      calc (-1 : ℂ) ^ (2 * k) = ((-1 : ℂ) ^ 2) ^ k := by simp [pow_mul]
        _ = 1 := by norm_num
    -- 1 = -1 矛盾
    have : (1 : ℂ) = -1 := by simpa [hpow] using h
    norm_num at this
  · -- m 奇 ⟹ (-1)^m = -1
    intro hm
    rcases hm with ⟨k, hk⟩
    subst m
    calc (-1 : ℂ) ^ (2 * k + 1) = (-1 : ℂ) ^ (2 * k) * (-1 : ℂ) := by simp [pow_succ]
      _ = ((-1 : ℂ) ^ 2) ^ k * (-1 : ℂ) := by simp [pow_mul]
      _ = -1 := by norm_num

/-- **奇阶翻转**: m 奇 ⟹ u 跨零点翻转 — 左右极限互为相反数。 -/
theorem flip_of_odd_order {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hm : Odd m)
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (_hg : g (zetaLine t₀) ≠ 0) (_hg_cont : ContinuousAt g (zetaLine t₀)) :
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) =
      -((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
  -- (-i)^m = -i^m ⟺ m 奇
  have hIm : (-I) ^ m = -(I ^ m) := by
    rcases hm with ⟨k, hk⟩
    subst m
    rw [show (-I : ℂ) = (-1 : ℂ) * I by ring]
    rw [mul_pow]
    have hneg1 : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
      calc
        (-1 : ℂ) ^ (2 * k + 1) = (-1 : ℂ) ^ (2 * k) * (-1 : ℂ) := by simp [pow_succ]
        _ = ((-1 : ℂ) ^ 2) ^ k * (-1 : ℂ) := by simp [pow_mul]
        _ = -1 := by norm_num
    rw [hneg1]
    ring
  rw [hIm]
  ring

/-- **偶阶通过**: m 偶 ⟹ u 跨零点连续通过 (左右极限相等, 可延拓)。 -/
theorem pass_of_even_order {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hm : Even m)
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (_hg : g (zetaLine t₀) ≠ 0) (_hg_cont : ContinuousAt g (zetaLine t₀)) :
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) =
      ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
  -- (-i)^m = i^m ⟺ m 偶
  have hIm : (-I) ^ m = I ^ m := by
    rcases hm with ⟨k, hk⟩
    subst m
    -- Even m = ∃ r, m = r + r ⟹ m = 2k (two_mul)
    have htwo : k + k = 2 * k := by omega
    rw [htwo]
    rw [show (-I : ℂ) = (-1 : ℂ) * I by ring]
    rw [mul_pow]
    have hneg1 : (-1 : ℂ) ^ (2 * k) = 1 := by
      calc
        (-1 : ℂ) ^ (2 * k) = ((-1 : ℂ) ^ 2) ^ k := by simp [pow_mul]
        _ = 1 := by norm_num
    rw [hneg1]
    ring
  rw [hIm]

/-- **翻转 ⟺ m 奇 (主定理)**: 由左右极限公式,
    u(t₀⁻) = -u(t₀⁺) ⟺ (-i)^m = -i^m ⟺ (-1)^m = -1 ⟺ m 奇。 -/
theorem flip_iff_odd {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    ((I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) =
        -((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))) ↔ Odd m := by
  constructor
  · -- 翻转 ⟹ m 奇: 反证 m 偶 ⟹ 相等, 与相反矛盾
    intro hflip
    by_contra hodd
    have heven : Even m := Nat.not_odd_iff_even.mp hodd
    have hpass := pass_of_even_order heven h_exp hg hg_cont
    -- 相等且相反 ⟹ u⁺ = 0
    have hzero : I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖) = 0 := by
      -- hflip (u⁺ = -u⁻) 与 hpass (u⁺ = u⁻) ⟹ u⁺ = -u⁺
      have hneg_self : I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖) =
          -(I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
        calc
          I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖) =
              -((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := hflip
          _ = -(I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by rw [← hpass]
      have hsum : 2 * (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) = 0 := by
        rw [two_mul]
        nth_rw 1 [hneg_self]
        ring
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hsum).resolve_left h2
    -- g(s₀)/|g(s₀)| ≠ 0 ⟹ i^m 非零 ⟹ 矛盾
    have hg_ratio_ne : g (zetaLine t₀) / ‖g (zetaLine t₀)‖ ≠ 0 := by
      exact div_ne_zero hg (by exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg))
    exact (mul_ne_zero (pow_ne_zero m (by norm_num : (I : ℂ) ≠ 0)) hg_ratio_ne) hzero
  · -- m 奇 ⟹ 翻转
    intro hm
    exact flip_of_odd_order hm h_exp hg hg_cont


  -- ============================================================
  -- T6n: 翻转 = π 相位跳桥 (2026-08-19)
  -- 用户方法论继续: 未证部分 (翻转计数 = 零点数) 用桥接推进。
  -- 翻转 (u⁻ = -u⁺, ① flip_of_odd_order) ⟹ u⁻/u⁺ = -1 = e^{iπ}:
  -- 左右对称方向的相位 (I^m 与 (-I)^m) 在对消后只剩 e^{iπ},
  -- 翻转 = π 相位跳 = e^{iπ} 桥的离散版 (与 e^{iπS} = u 平行)。
  -- 翻转计数 = 零点数的最后拼装: 每跨零点 θ_ζ 跳 π (此桥) +
  -- T6e 整数层 (2θ_ζ - θ_χ = 2πim) + θ_χ 连续 ⟹ 层跳 1。
  -- ============================================================

/-- **翻转 = π 相位跳**: u(t₀⁻)/u(t₀⁺) = -1 — 左右对称方向的相位
    (I^m 与 (-I)^m) 在比值中对消, 剩下符号 -1 = e^{iπ}。
    翻转 (m 奇, ①) 的比值形式: 相位跳 π 而非任意相位。 -/
theorem flip_phase_jump_pi {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hm : Odd m)
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) /
      ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) = -1 := by
  -- u⁻ ≠ 0 (G = g/|g| ≠ 0)
  have hden : (-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by simp : (-I : ℂ) ≠ 0)) (div_ne_zero hg (by simpa using hg))
  -- 翻转: u⁺ = -u⁻ (flip_of_odd_order) ⟹ u⁺/u⁻ = -1
  have hflip := flip_of_odd_order hm h_exp hg hg_cont
  calc
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) /
        ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))
        = (-((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖))) /
            ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) := by
          rw [hflip]
    _ = -1 := by
      field_simp [hden, (norm_ne_zero_iff.mpr hg : ‖g (zetaLine t₀)‖ ≠ 0)]

/-- **翻转 = e^{iπ} (指数形式)**: u(t₀⁻)/u(t₀⁺) = e^{iπ} —
    e^{iπ} 桥的离散版: 翻转 = π 相位跳 = 单位元 -1 的指数表示。
    与 e^{iπS(T)} = u(T) 平行: 连续相位用 e^{iπS}, 翻转用 e^{iπ}。 -/
theorem flip_phase_jump_exp {t₀ : ℝ} {m : ℕ} {g : ℂ → ℂ}
    (hm : Odd m)
    (h_exp : ∀ᶠ s in 𝓝 (zetaLine t₀), riemannZeta s = (s - zetaLine t₀) ^ m * g s)
    (hg : g (zetaLine t₀) ≠ 0) (hg_cont : ContinuousAt g (zetaLine t₀)) :
    (I ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) /
      ((-I) ^ m * (g (zetaLine t₀) / ‖g (zetaLine t₀)‖)) = Complex.exp (↑Real.pi * Complex.I) := by
  -- -1 = e^{iπ} (exp_pi_mul_I)
  rw [flip_phase_jump_pi hm h_exp hg hg_cont]
  rw [Complex.exp_pi_mul_I]


/-- Re s < 0 无零点 (s 非负整数): 函数方程镜像 riemannZeta_ne_zero_of_one_le_re.
    ζ(s) = 0 ⟹ ζ(1-s) = F(s)·0 = 0, 但 1-s.re > 1 处 ζ ≠ 0. -/
theorem riemannZeta_ne_zero_of_re_lt_zero (s : ℂ) (hs : s.re < 0)
    (hs_int : ∀ n : ℕ, s ≠ -n) : riemannZeta s ≠ 0 := by
  intro hz
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hfe := riemannZeta_one_sub (s := s) hs_int hs_ne_one
  have hzsub : riemannZeta (1 - s) = 0 := by
    rw [hfe, hz]
    simp
  -- 1-s.re = 1 - s.re > 1 ⟹ ζ(1-s) ≠ 0
  have hgeom : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hs]
  exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hgeom) hzsub

/-- Re s = 0 无零点 (s ≠ 0): 函数方程在 1-s 处镜像. -/
theorem riemannZeta_ne_zero_of_re_eq_zero (s : ℂ) (hs : s.re = 0) (hs0 : s ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hz
  -- 函数方程在 1-s 处: ζ(s) = F(1-s)·ζ(1-s); F 因子全非零 ⟹ ζ(1-s) = 0
  have hs_int : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h
    have hre : (1 - s).re = (-(n : ℂ)).re := by rw [h]
    rw [Complex.sub_re, Complex.one_re, hs] at hre
    have : ((-(n : ℂ)).re) ≤ 0 := by simp
    linarith
  have hsub_ne_one : 1 - s ≠ 1 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by norm_num
  have hfe := riemannZeta_one_sub (s := 1 - s) hs_int hsub_ne_one
  -- hfe : ζ(s) = 2·(2π)^(-(1-s))·Γ(1-s)·cos(π(1-s)/2)·ζ(1-s)
  -- 因子分解: 2 ≠ 0, (2π)^(-(1-s)) ≠ 0, Γ(1-s) ≠ 0, cos(π(1-s)/2) ≠ 0
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have htwo_pi : (2 * ↑Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero htwo (by exact_mod_cast Real.pi_ne_zero)
  have hcpow : (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).mpr (Or.inl htwo_pi)
  have hgamma : Complex.Gamma (1 - s) ≠ 0 := by
    exact Complex.Gamma_ne_zero hs_int
  -- cos(π(1-s)/2) ≠ 0: s.re = 0 且 s ≠ 0 ⟹ s ∉ 2ℤ ⟹ 1-s ∉ 2ℤ+1 ⟹ cos ≠ 0
  have hs_not_int : ∀ k : ℤ, s ≠ 2 * (k : ℂ) := by
    intro k h
    have hre : s.re = (2 * (k : ℝ) : ℝ) := by
      rw [h]
      simp
    have hk0 : (k : ℝ) = 0 := by
      rw [hs] at hre
      nlinarith
    have hk0' : k = 0 := by exact_mod_cast hk0
    apply hs0
    rw [h, hk0']
    norm_num
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    -- π(1-s)/2 = (2k+1)π/2 ⟹ 1-s = 2k+1 ⟹ s = -2k ∈ 2ℤ, 矛盾
    have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hmul : ↑Real.pi * (1 - s) = (2 * (k : ℂ) + 1) * ↑Real.pi := by
      calc
        ↑Real.pi * (1 - s) = (↑Real.pi * (1 - s) / 2) * 2 := by field_simp [h2]
        _ = ((2 * (k : ℂ) + 1) * ↑Real.pi / 2) * 2 := by rw [hk]
        _ = (2 * (k : ℂ) + 1) * ↑Real.pi := by field_simp [h2]
    have hk' : 1 - s = ↑(2 * k + 1) := by
      have hc : 1 - s = 2 * (k : ℂ) + 1 := by
        exact mul_right_cancel₀ hpi (by simpa [mul_comm] using hmul)
      simpa [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hc
    have hs2 : s = 2 * ((-k : ℤ) : ℂ) := by
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 - ↑(2 * k + 1) := by rw [hk']
        _ = (2 : ℂ) * ↑(-k) := by
          rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_neg]
          ring
    exact (hs_not_int (-k)) hs2
  have hF : (2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ)
      * Complex.Gamma (1 - s) * Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hcpow) hgamma) hcos
  -- ζ(s) = F·ζ(1-s) = 0 且 F ≠ 0 ⟹ ζ(1-s) = 0 ⟹ 矛盾 (1 ≤ Re(1-s), 1-s ≠ 1)
  have hzsub : riemannZeta (1 - s) = 0 := by
    have hFz : (2 : ℂ) * (2 * ↑Real.pi : ℂ) ^ (-(1 - s) : ℂ)
        * Complex.Gamma (1 - s) * Complex.cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) = 0 := by
      rw [← hfe]
      simpa using hz
    exact (mul_eq_zero.mp hFz).resolve_left hF
  have hgeom : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re, hs]
    norm_num
  have hsub_ne_one' : 1 - s ≠ 1 := hsub_ne_one
  exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hgeom) hzsub

/-- 非平凡零点全在临界带: ζ(s) = 0 (排除平凡零点与极点, 排除负整数) ⟹ 0 < Re s < 1. -/
theorem nontrivial_zero_in_critical_strip {s : ℂ} (hz : riemannZeta s = 0)
    (h_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (hs1 : s ≠ 1)
    (hs_int : ∀ n : ℕ, s ≠ -n) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · -- 0 < s.re: 反证, s.re ≤ 0
    by_contra h
    have hle : s.re ≤ 0 := le_of_not_gt h
    rcases lt_or_eq_of_le hle with hs_neg | hs_zero
    · exact (riemannZeta_ne_zero_of_re_lt_zero s hs_neg hs_int) hz
    · have hs0 : s ≠ 0 := by
        intro h
        rw [h, riemannZeta_zero] at hz
        norm_num at hz
      exact (riemannZeta_ne_zero_of_re_eq_zero s hs_zero hs0) hz
  · -- s.re < 1: 反证, 1 ≤ s.re ⟹ ζ ≠ 0
    by_contra h
    have hge : 1 ≤ s.re := le_of_not_gt h
    exact (riemannZeta_ne_zero_of_one_le_re (s := s) hge) hz
end RiemannUnifiedObservation

namespace ZeroRelative

/-- 二维旋转代数 a + b·J (矩阵表示 [[a,-b],[b,a]], ≅ ℂ)。 -/
structure ComplexAxis where
  a : ℝ
  b : ℝ

namespace ComplexAxis

/-- 加法 (分量) -/
def add (x y : ComplexAxis) : ComplexAxis := ⟨x.a + y.a, x.b + y.b⟩

/-- 相反数 -/
def neg (x : ComplexAxis) : ComplexAxis := ⟨-x.a, -x.b⟩

/-- 零 -/
def zero : ComplexAxis := ⟨0, 0⟩

/-- 一 -/
def one : ComplexAxis := ⟨1, 0⟩

/-- 90° 旋转 J (J² = -1) -/
def J : ComplexAxis := ⟨0, 1⟩

/-- 乘法 (复数乘法): (a₁+b₁J)(a₂+b₂J) = (a₁a₂-b₁b₂) + (a₁b₂+a₂b₁)J -/
def mul (x y : ComplexAxis) : ComplexAxis :=
  ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a⟩

/-- 减法 (分量) -/
def sub (x y : ComplexAxis) : ComplexAxis := ⟨x.a - y.a, x.b - y.b⟩

instance instAdd : Add ComplexAxis := ⟨add⟩
instance instNeg : Neg ComplexAxis := ⟨neg⟩
instance instSub : Sub ComplexAxis := ⟨sub⟩
instance instZero : Zero ComplexAxis := ⟨zero⟩
instance instOne : One ComplexAxis := ⟨one⟩
instance instMul : Mul ComplexAxis := ⟨mul⟩

@[ext] theorem ext (x y : ComplexAxis) (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      simp at ha hb
      simp [ha, hb]

/-- 抬升: 实数轴嵌入 (标量部分, 保加法乘法) -/
def lift (t : ℝ) : ComplexAxis := ⟨t, 0⟩

/-- 范数: 半径平方 (norm z = a² + b²) -/
def norm (z : ComplexAxis) : ℝ := z.a ^ 2 + z.b ^ 2

/-- 素数圆: 圆心 0 半径 √p (素数 p 的两平方和整点所在)。 -/
def primeCircle (p : ℕ) : Set ComplexAxis := {z : ComplexAxis | norm z = (p : ℝ)}

/-- 临界线圆: 圆心 (1,0) 半径 1 (临界线蜷曲下的像, 经过 0 和 2)。 -/
def criticalCircle : Set ComplexAxis := {w : ComplexAxis | norm (w - lift 1) = 1}
end ComplexAxis
end ZeroRelative

namespace ComplexPlaneIntersections

open ZeroRelative
open ZeroRelative.ComplexAxis

/-- 纵轴 (虚轴) 与临界圆: t·J ∈ criticalCircle ↔ t = 0
    (虚轴与临界圆只交于原点; 对比实轴交 {0, 2})。 -/
theorem imagAxis_inter_criticalCircle (t : ℝ) :
    (ComplexAxis.lift t * J : ComplexAxis) ∈ criticalCircle ↔ t = 0 := by
  constructor
  · intro h
    have hn : ComplexAxis.norm (ComplexAxis.lift t * J - ComplexAxis.lift 1) = 1 := by
      simpa [criticalCircle] using h
    -- ComplexAxis.norm ⟨-1, t⟩ = 1 + t² = 1 ⟹ t = 0
    have heq : ComplexAxis.lift t * J - ComplexAxis.lift 1 = ⟨-1, t⟩ := by
      change ComplexAxis.sub (ComplexAxis.mul (ComplexAxis.lift t) J) (ComplexAxis.lift 1) = ⟨-1, t⟩
      ext <;> simp [ComplexAxis.lift, J, mul, sub]
    have hcalc : 1 + t ^ 2 = 1 := by
      rw [heq] at hn
      simpa [ComplexAxis.norm] using hn
    nlinarith
  · intro ht
    subst ht
    simp only [criticalCircle]
    change ComplexAxis.norm (ComplexAxis.sub (ComplexAxis.mul (ComplexAxis.lift 0) J) (ComplexAxis.lift 1)) = 1
    change ComplexAxis.norm (ComplexAxis.sub (ComplexAxis.mul ⟨0, 0⟩ ⟨0, 1⟩) ⟨1, 0⟩) = 1
    norm_num [ComplexAxis.mul, ComplexAxis.norm, ComplexAxis.sub]

/-- 横轴与素数圆: ComplexAxis.lift r ∈ primeCircle p ↔ r² = p (交于 ±√p)。 -/
theorem realAxis_inter_primeCircle (r : ℝ) (p : ℕ) :
    (ComplexAxis.lift r : ComplexAxis) ∈ primeCircle p ↔ r ^ 2 = (p : ℝ) := by
  simp [primeCircle, ComplexAxis.norm, ComplexAxis.lift, sub]

/-- 纵轴与素数圆: t·J ∈ primeCircle p ↔ t² = p (交于 ±i√p)。 -/
theorem imagAxis_inter_primeCircle (t : ℝ) (p : ℕ) :
    (ComplexAxis.lift t * J : ComplexAxis) ∈ primeCircle p ↔ t ^ 2 = (p : ℝ) := by
  change ComplexAxis.mul ⟨t, 0⟩ ⟨0, 1⟩ ∈ primeCircle p ↔ t ^ 2 = (p : ℝ)
  simp [primeCircle, ComplexAxis.norm, ComplexAxis.mul, pow_two]

/-- 素数圆 3 与临界圆: z = 3/2 + √3/2·J 在交集中
    (ComplexAxis.norm = 9/4 + 3/4 = 3; ComplexAxis.norm(z-1) = 1/4 + 3/4 = 1)。 -/
theorem prime3Circle_inter_criticalCircle :
    (⟨3 / 2, Real.sqrt 3 / 2⟩ : ComplexAxis) ∈ primeCircle 3 ∧
      (⟨3 / 2, Real.sqrt 3 / 2⟩ : ComplexAxis) ∈ criticalCircle := by
  have hsq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    have h1 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  constructor
  · simp [primeCircle, ComplexAxis.norm]
    nlinarith
  · change ComplexAxis.norm (ComplexAxis.sub (⟨3 / 2, Real.sqrt 3 / 2⟩ : ComplexAxis) (ComplexAxis.lift 1)) = 1
    simp [ComplexAxis.norm, ComplexAxis.lift, sub]
    nlinarith

/-- 素数 p ≥ 5 的素数圆与临界圆不相交
    (半径 √p 的圆与圆心 (1,0) 半径 1 的圆: 相交 ⟹ p ≤ 4)。 -/
theorem primeCircle_inter_criticalCircle_ge5 {p : ℕ} (hp5 : 5 ≤ p) :
    primeCircle p ∩ criticalCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have hn : ComplexAxis.norm z = (p : ℝ) := hz.1
    have hc : ComplexAxis.norm (z - ComplexAxis.lift 1) = 1 := hz.2
    -- a = p/2 (从 ComplexAxis.norm(z-1) = ComplexAxis.norm z - 2a + 1)
    have ha : z.a = (p : ℝ) / 2 := by
      have h1 : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [ComplexAxis.norm] using hn
      have h2 : (z.a - 1) ^ 2 + z.b ^ 2 = 1 := by
        have hza : (z - ComplexAxis.lift 1).a = z.a - 1 := by
          change (ComplexAxis.sub z (ComplexAxis.lift 1)).a = z.a - 1
          simp [ComplexAxis.lift, sub]
        have hzb : (z - ComplexAxis.lift 1).b = z.b := by
          change (ComplexAxis.sub z (ComplexAxis.lift 1)).b = z.b
          simp [ComplexAxis.lift, sub]
        rw [ComplexAxis.norm] at hc
        rw [hza, hzb] at hc
        exact hc
      nlinarith
    -- b² = p - p²/4 < 0 (p ≥ 5) — 矛盾
    have hb2 : z.b ^ 2 = (p : ℝ) - (p : ℝ) ^ 2 / 4 := by
      have h1 : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [ComplexAxis.norm] using hn
      nlinarith
    have hneg : (p : ℝ) - (p : ℝ) ^ 2 / 4 < 0 := by
      have hpR : (4 : ℝ) < (p : ℝ) := by
        have hp5' : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
        nlinarith
      nlinarith
    nlinarith
  · intro hz
    simp at hz
end ComplexPlaneIntersections

/-!
# Hardy Z (翻转次数缺口 1+1b) — 自包含 0pat, 只 import Mathlib
-/
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
      change ContinuousAt ((fun _ : ℂ => (1 : ℂ)) - _root_.id) s
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
