/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/ContinuumConstructible — ★连续统的内生形式化: 两基点方向对 → 还原点闭包 (定义层零 Nat)

R163 (2026-08-15) 观点链: 对称性 = 降维 (反射固定点 = 还原点 = 中点);
对称方向的每个方向从结构承载信息角度有两个基点; 连续统 = 对称性降维闭包.

R150/R151 定义层内生化 (修正: 原 patGrid = {2π·j/N : N j ∈ ℕ} 用 ℕ 索引 —
违反内生生成纪律; 新版定义层零 Nat):

  两基点方向对:  base0 = 0, base1 = 2π (方向声明成对, R136/R144/R145)
  降维生成规则:  对称对 (x, y) 的还原点 = 中点 (x+y)/2 (反射固定点, R163)
  内生闭包:      patGrid' = 含 {base0, base1} 且对还原点封闭的最小集合
                 (归纳定义 — 生成闭包, 零 Nat)

表示定理 (结论层允许 Nat): patGrid' = {2π·k/2ᵐ : 0 ≤ k ≤ 2ᵐ} (dyadic 有理 × 2π)
  — 这是"结构生成出什么"的表示, 不是定义 (R163: 减少一个就得成对减少 —
  生成每步成对使用, 分子范围随细分成对扩展)

Main theorems:

1. `InPat_dyadic`: 内生闭包元素 ⟹ dyadic 表示 (结构归纳, 零 Nat).
2. `dyadic_InPat`: dyadic 且 0 ≤ k ≤ 2ᵐ ⟹ 内生闭包元素 (表示定理, m 归纳).
3. `patGrid'_dense`: 内生格点稠密于 [0, 2π] (二分, 元层 Nat — 允许).
4. `continuum_in_constructible_closure`: 连续统 = 内生格点的闭包 (R151 内生版).
-/

namespace ZeroRelative

namespace ContinuumConstructible

open scoped Real

noncomputable section

/-- 两基点方向对 (方向声明成对, R136): 端点 0 与 2π. -/
def base0 : ℝ := 0

def base1 : ℝ := 2 * Real.pi

/-- 对称性降维 (R163): 对称对 (x, y) 的还原点 = 反射固定点 = 中点. -/
def midpoint (x y : ℝ) : ℝ := (x + y) / 2

/-- 内生闭包 (定义层零 Nat): 含两基点且对还原点封闭的最小集合 (归纳生成). -/
inductive InPat : ℝ → Prop
  | base0 : InPat base0
  | base1 : InPat base1
  | mid {x y : ℝ} : InPat x → InPat y → InPat (midpoint x y)

/-- patGrid': 内生闭包作为集合. -/
def patGrid' : Set ℝ := {x | InPat x}

/-- 表示定理 (结论层允许 Nat): dyadic 表示 — 2π·k/2ᵐ, 分子 0 ≤ k ≤ 2ᵐ. -/
def Dyadic (x : ℝ) : Prop :=
  ∃ k m : ℕ, 0 ≤ k ∧ k ≤ 2 ^ m ∧ x = 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ m

/-! ## 1. 内生闭包元素 ⟹ dyadic 表示 (结构归纳, 零 Nat) -/

lemma base0_dyadic : Dyadic base0 := by
  refine ⟨0, 0, by norm_num, by norm_num, ?_⟩
  norm_num [base0]

lemma base1_dyadic : Dyadic base1 := by
  refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
  norm_num [base1]

lemma mid_dyadic {x y : ℝ} (hx : Dyadic x) (hy : Dyadic y) : Dyadic (midpoint x y) := by
  rcases hx with ⟨k1, m1, hk1a, hk1b, hx⟩
  rcases hy with ⟨k2, m2, hk2a, hk2b, hy⟩
  -- 通分: (k1/2^m1 + k2/2^m2)/2 = (k1·2^m2 + k2·2^m1) / 2^(m1+m2+1)
  refine ⟨k1 * 2 ^ m2 + k2 * 2 ^ m1, m1 + m2 + 1, by positivity, ?_, ?_⟩
  · -- k1·2^m2 + k2·2^m1 ≤ 2^(m1+m2+1) = 2^(m1+m2)·2
    have hk1 : k1 * 2 ^ m2 ≤ 2 ^ m1 * 2 ^ m2 := by
      exact Nat.mul_le_mul_right (2 ^ m2) hk1b
    have hk2 : k2 * 2 ^ m1 ≤ 2 ^ m2 * 2 ^ m1 := by
      exact Nat.mul_le_mul_right (2 ^ m1) hk2b
    have hsum : k1 * 2 ^ m2 + k2 * 2 ^ m1 ≤ 2 * (2 ^ m1 * 2 ^ m2) := by
      nlinarith
    have hpow : 2 * (2 ^ m1 * 2 ^ m2) = 2 ^ (m1 + m2 + 1) := by
      rw [pow_add, pow_succ]
      ring
    omega
  · -- 数值: (x + y)/2 = 2π·(k1·2^m2 + k2·2^m1)/2^(m1+m2+1)
    rw [midpoint, hx, hy]
    field_simp [pow_pos (by norm_num : (0 : ℝ) < 2)]
    rw [pow_add, pow_succ]
    ring

/-- **内生闭包元素 ⟹ dyadic 表示** (结构归纳, 零 Nat): patGrid' ⊆ dyadic. -/
theorem InPat_dyadic {x : ℝ} (h : InPat x) : Dyadic x := by
  induction h with
  | base0 => exact base0_dyadic
  | base1 => exact base1_dyadic
  | mid hx hy ihx ihy => exact mid_dyadic ihx ihy

/-! ## 2. dyadic ⟹ 内生闭包 (表示定理, m 归纳 — 结论层允许 Nat) -/

lemma InPat_mid_closed {x y : ℝ} (hx : InPat x) (hy : InPat y) : InPat (midpoint x y) :=
  InPat.mid hx hy

/-- **dyadic 且 0 ≤ k ≤ 2ᵐ ⟹ 内生闭包元素** (m 归纳): 每步成对细分 (R163:
减少一个就得成对减少 — 生成成对, 分子范围成对扩展). -/
theorem dyadic_InPat (k m : ℕ) (hk : k ≤ 2 ^ m) : InPat (2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ m) := by
  induction m with
  | zero =>
      -- m = 0: k ∈ {0, 1} (k ≤ 2^0 = 1): base0 / base1
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · simpa [base0] using InPat.base0
      · simpa [base1] using InPat.base1
  | succ m ih =>
      -- k ≤ 2^(m+1): k = 2j 或 2j+1, 中点 (j/2^m, (j+1)/2^m) 生成
      let j := k / 2
      have hk_eq : k = 2 * j ∨ k = 2 * j + 1 := by
        have hdm : k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
        have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases hmod with h | h
        · left; omega
        · right; omega
      have hk_le : k ≤ 2 * 2 ^ m := by
        simpa [pow_succ, Nat.mul_comm] using hk
      rcases hk_eq with hk2 | hk2
      · -- k = 2j: 2j/2^(m+1) = j/2^m (IH)
        have hj : j ≤ 2 ^ m := by omega
        have hval : 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ (m + 1)
            = 2 * Real.pi * (j : ℝ) / (2 : ℝ) ^ m := by
          rw [hk2]
          field_simp [pow_pos (by norm_num : (0 : ℝ) < 2)]
          rw [pow_succ]
          ring
        rw [hval]
        exact ih j hj
      · -- k = 2j+1: 中点 (j/2^m, (j+1)/2^m)
        have hj1 : j ≤ 2 ^ m := by omega
        have hj2 : j + 1 ≤ 2 ^ m := by omega
        have hleft := ih j hj1
        have hright := ih (j + 1) hj2
        have hmid : midpoint (2 * Real.pi * (j : ℝ) / (2 : ℝ) ^ m)
            (2 * Real.pi * ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m)
            = 2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ (m + 1) := by
          rw [hk2]
          field_simp [pow_pos (by norm_num : (0 : ℝ) < 2)]
          rw [pow_succ]
          ring
        rw [← hmid]
        exact InPat_mid_closed hleft hright

/-! ## 3. 内生格点稠密于 [0, 2π] (二分, 元层 Nat) -/

/-- **内生格点稠密**: 任意 θ ∈ [0, 2π] 被 patGrid' 任意精度逼近 (二分 m 次,
元层 Nat — 表示定理层, 允许). -/
theorem patGrid'_dense (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
    ∀ ε : ℝ, 0 < ε → ∃ y ∈ patGrid', |θ - y| ≤ ε := by
  intro ε hε
  -- 取 m 使 2π/2^m ≤ ε (阿基米德: 2^m 无界)
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscale : 0 < 2 * Real.pi := by positivity
  -- 存在 m : ℕ 使 2π / 2^m ≤ ε: 取 m 使 2^m ≥ 2π/ε
  let target : ℝ := 2 * Real.pi / ε
  have htarget : 0 ≤ target := by positivity
  rcases exists_nat_ge target with ⟨M, hM⟩
  let m := M
  have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ m := le_rfl
  -- 二分: 存在 j ≤ 2^m 使 |θ − 2π·j/2^m| ≤ 2π/2^m
  have hg : ∃ j : ℕ, j ≤ 2 ^ m ∧ |θ - 2 * Real.pi * (j : ℝ) / (2 : ℝ) ^ m| ≤
      2 * Real.pi / (2 : ℝ) ^ m := by
    -- 取 j = ⌊θ·2^m/(2π)⌋ 的最近整数
    let q : ℝ := θ * (2 : ℝ) ^ m / (2 * Real.pi)
    have hq : 0 ≤ q := by positivity
    let j : ℕ := Int.toNat ⌊q⌋
    have hj0 : (j : ℝ) ≤ q := by
      have hf : (⌊q⌋ : ℝ) ≤ q := Int.floor_le q
      dsimp [j]
      exact_mod_cast hf
    have hj1 : q < (j : ℝ) + 1 := by
      have hf : q < (⌊q⌋ : ℝ) + 1 := Int.lt_floor_add_one q
      have hnonneg : 0 ≤ ⌊q⌋ := by
        exact_mod_cast (Int.floor_nonneg.mpr hq)
      dsimp [j]
      rw [Int.toNat_of_nonneg hnonneg]
      exact_mod_cast hf
    -- j ≤ 2^m
    have hjle : (j : ℝ) ≤ (2 : ℝ) ^ m := by
      have : q ≤ (2 : ℝ) ^ m / (2 * Real.pi) * (2 * Real.pi) := by
        calc
          q = θ * (2 : ℝ) ^ m / (2 * Real.pi) := rfl
          _ ≤ (2 * Real.pi) * (2 : ℝ) ^ m / (2 * Real.pi) := by
            gcongr
            exact hθ₂
          _ = (2 : ℝ) ^ m := by field_simp [ne_of_gt hscale]
      have : q ≤ (2 : ℝ) ^ m := by
        calc
          q ≤ (2 * Real.pi) * (2 : ℝ) ^ m / (2 * Real.pi) := this
          _ = (2 : ℝ) ^ m := by field_simp [ne_of_gt hscale]
      exact le_trans hj0 this
    have hjle_nat : j ≤ 2 ^ m := by
      exact_mod_cast hjle
    -- 误差: |θ − 2π·j/2^m| ≤ 2π/2^m (j 是 q 的 floor: θ = q·2π/2^m)
    have hmain : |θ - 2 * Real.pi * (j : ℝ) / (2 : ℝ) ^ m| ≤
        2 * Real.pi / (2 : ℝ) ^ m := by
      have hθq : θ = q * (2 * Real.pi) / (2 : ℝ) ^ m := by
        field_simp [ne_of_gt hscale, pow_pos hpos m]
        dsimp [q]
        ring
      -- |q·2π/2^m − j·2π/2^m| = |q − j|·2π/2^m ≤ 2π/2^m (q ∈ [j, j+1))
      have hqj1 : q - (j : ℝ) < 1 := by
        have : q < (j : ℝ) + 1 := hj1
        linarith
      have hqj0 : 0 ≤ q - (j : ℝ) := by linarith
      have habs : |q - (j : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg hqj0]
        exact le_of_lt hqj1
      rw [hθq]
      calc
        |q * (2 * Real.pi) / (2 : ℝ) ^ m - 2 * Real.pi * (j : ℝ) / (2 : ℝ) ^ m|
            = |(q - (j : ℝ)) * (2 * Real.pi) / (2 : ℝ) ^ m| := by
              field_simp [pow_pos hpos m]
              ring
        _ ≤ 1 * (2 * Real.pi) / (2 : ℝ) ^ m := by
          have hden : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) m
          rw [abs_div, abs_mul]
          rw [abs_of_pos hden, abs_of_pos hscale]
          gcongr
          exact habs
        _ = 2 * Real.pi / (2 : ℝ) ^ m := by ring
    exact ⟨j, hjle_nat, hmain⟩
  rcases hg with ⟨j, hjle, hdist⟩
  -- 2π/2^m ≤ ε (m 的选择)
  have hme : 2 * Real.pi / (2 : ℝ) ^ m ≤ ε := by
    have hpow_le : ε * (2 : ℝ) ^ m ≥ 2 * Real.pi := by
      have hM : target ≤ (M : ℝ) := hM
      have hMpow : (M : ℝ) ≤ (2 : ℝ) ^ m := by
        have hM2 : M ≤ 2 ^ M := by
          induction M with
          | zero => simp
          | succ M ih =>
              have h1 : M + 1 ≤ 2 ^ M + 1 := by omega
              have h2 : 2 ^ M + 1 ≤ 2 ^ (M + 1) := by
                rw [pow_succ]
                have : 2 ^ M + 1 ≤ 2 ^ M + 2 ^ M := by omega
                simpa
              omega
        have hmono : (M : ℝ) ≤ (2 : ℝ) ^ M := by exact_mod_cast hM2
        simpa [m]
      have : target ≤ (2 : ℝ) ^ m := le_trans hM hMpow
      dsimp [target] at this
      have : 2 * Real.pi / ε ≤ (2 : ℝ) ^ m := this
      have : 2 * Real.pi ≤ (2 : ℝ) ^ m * ε := by
        exact (div_le_iff₀ hε).mp this
      nlinarith
    exact (div_le_iff₀ (pow_pos hpos m)).mpr hpow_le
  -- 组合: y = 2π·j/2^m ∈ patGrid' (dyadic_InPat), |θ − y| ≤ 2π/2^m ≤ ε
  refine ⟨2 * Real.pi * (j : ℝ) / (2 : ℝ) ^ m, ?_, ?_⟩
  · exact dyadic_InPat j m hjle
  · exact le_trans hdist hme

/-! ## 4. 连续统 = 内生格点的闭包 (R151 内生版) -/

/-- **连续统 = 内生格点的闭包**: 任意 x ∈ [0, 2π] 属于 patGrid' 的闭包
(R163: 对称性降维闭包 — 定义层零 Nat, 两基点方向对生成). -/
theorem continuum_in_constructible_closure (x : ℝ) (hx₁ : 0 ≤ x) (hx₂ : x ≤ 2 * Real.pi) :
    x ∈ closure patGrid' := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases patGrid'_dense x hx₁ hx₂ (ε / 2) (by positivity) with ⟨y, hy, hle⟩
  refine ⟨y, hy, ?_⟩
  have hlt : |x - y| < ε := by
    have hε' : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt hle hε'
  rwa [Real.dist_eq]

end ContinuumConstructible

end ZeroRelative
