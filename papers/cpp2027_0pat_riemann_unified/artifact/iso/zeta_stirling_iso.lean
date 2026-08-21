import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# T6i: χ 圈数渐近 (Stirling) — 对消法的显式相位刻度

χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2) 是函数方程乘子: ζ(s) = χ(s)·ζ(1-s)。
χ 沿临界线是**单位圆上的路径** (|χ(1/2+it)| = 1, 反射公式), 其相位
θ_χ(T) = arg χ(1/2+iT) 是"显式相位刻度": 圈数 = θ_χ(T)/2π 是
零点计数 N(T) = (1/π)θ_χ(T) + S(T) + 1 的主项 (参数原理, 任务③)。

**Stirling 渐近** (本文件的核心声明):
    θ_χ(T) = (T/2)·log(T/2π) - T/2 - π/8 + O(1/T)   (Backlund)
    ⟹ 零点计数 N(T) = (T/2π)·log(T/2πe) + 7/8 + S(T) + O(1/T)
    (N = θ_χ/π + 1 + S: 常数 1 + (-1/8) = 7/8)

第一层 (本文件): 精确部分 — 反射公式:
    χ(s)·χ(1-s) = 1 (s ∉ ℤ: 乘子自反)
    |χ(1/2+it)| = 1 (χ 临界线 = 单位圆路径)
    θ_χ(T) 的定义与分解 (arg = T·log(2π) - arg Γ(1/2+iT) + arg sin)
第二层 (Stirling 主项): log|Γ| 精确 + Im log Γ 的 Binet 展开 (后续)。

对消法 (pat 本质, 2026-08-19): χ 的显式相位是"参照相位", 用 θ_χ
对消 ζ 的隐式相位 (素数叠加), 残差 S(T) 是整数层 (T6e/T6g)。

隔离文件 (mathlib-only)。 -/

noncomputable section

open Complex
open scoped Topology ComplexConjugate

namespace RiemannUnifiedObservation

/-- χ(s) = 2·(2π)^{s-1}·Γ(1-s)·sin(πs/2): 函数方程乘子 (显式相位)。 -/
def chi (s : ℂ) : ℂ :=
  2 * (2 * ↑Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
    Complex.sin (↑Real.pi * s / 2)

/-- χ 共轭对称: χ(s̄) = conj (χ s) (系数逐项共轭: 2π 实数 / Γ / sin)。 -/
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

end RiemannUnifiedObservation
