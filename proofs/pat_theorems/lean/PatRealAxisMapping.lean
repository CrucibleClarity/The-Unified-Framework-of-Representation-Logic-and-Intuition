/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Formal.Toolkit.PatParityPrime
import Formal.Toolkit.PatPrimeGapPhase
import Formal.Toolkit.PatCollatz

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatRealAxisMapping — ★实数轴在 pat 上的映射架构图景

User request (2026-08-13): "那是否有可能，实数轴视角下丢失了某一个槽？
先形式化一个实数轴在pat上的映射架构图景出来，我们好了解pat上哪些
位置实数轴上永远不出现."

## 映射架构: 实数轴 (整数子集) → pat 4 次单位根槽位

4 次单位根投影 n ↦ I^n (R175: 奇偶 = 实/虚轴; R141: 4 槽环) 把实数
轴上的点 (自然数/素数/轨道) 映射到 4 个槽:

| 实数轴子集 | 槽位 (n mod 4) | 覆盖 |
|---|---|---|
| 自然数 ℕ | {0, 1, 2, 3} | 全覆盖 |
| 偶数 | {0, 2} | 实轴 (R175) |
| 奇数 | {1, 3} | 虚轴 (R175) |
| **素数** | {1, 2, 3} | **★缺 0 槽** (p mod 4 ≠ 0) |
| **考拉兹循环 {1,4,2}** | {0, 1, 2} | **★缺 3 槽** |

★关键观测 (用户问题的答案):

1. **素数像永不落 0 槽** (I^p ≠ 1): p mod 4 = 0 ⟺ 4 | p ⟺ p = 4k
   (k ≥ 1) 是合数 — 素数永不 ≡ 0 (mod 4), 所以素数在 pat 上的像
   {I, -1, -I} 缺 0 槽 (+1). **pat 的 +1 位置是素数永远不出现的
   位置** — 素数是"少一个槽"的实数轴子集.
2. **考拉兹循环 {1, 4, 2} 像缺 3 槽** (无 -I): 1 ≡ 1, 4 ≡ 0,
   2 ≡ 2 (mod 4) — 循环中永不出现 ≡ 3 (mod 4) 的数, 所以循环的
   pat 像 {I, 1, -1} 缺 3 槽 (-I). 循环内部 1 → 4 → 2 的相位是
   1 槽 → 0 槽 → 2 槽, 永远跳过 3 槽.
3. **映射架构 (图景)**: 实数轴的不同子集在 pat 上覆盖不同的槽位
   组合 — 每个子集都有"永远不出现"的位置:
   - 素数: 永不落 +1 (0 槽, 实轴正侧).
   - 考拉兹循环: 永不落 -I (3 槽, 虚轴负侧).
   这就是"实数轴视角下丢失的槽": 不是实数轴本身丢失, 而是其子集
   (素数/轨道) 在 pat 投影下对应空缺槽位.

Main theorems (本文件, 全部只锚本框架):

1. `prime_mod_four_never_zero`: 素数 p 永不 ≡ 0 (mod 4) — 4k 是
   合数 (k ≥ 1).
2. `prime_pow_I_never_one`: ★素数像永不落 0 槽 — I^p ≠ 1 (4 | p
   ⟺ p = 4k 合数).
3. `collatz_cycle_mod_slots`: 循环 {1, 4, 2} 的槽位 = {0, 1, 2}:
   1 % 4 = 1 ∧ 4 % 4 = 0 ∧ 2 % 4 = 2.
4. `collatz_cycle_pow_never_neg_I`: ★循环像永不落 3 槽 — I^1 ≠ -I ∧
   I^4 ≠ -I ∧ I^2 ≠ -I.
5. `real_axis_pat_mapping_perspective`: 全景 — 素数缺 0 槽 ∧ 循环
   缺 3 槽 — 映射架构图景.
-/

namespace ZeroRelative

namespace PatRealAxisMapping

/-! ## 1. 素数永不 ≡ 0 (mod 4)

p mod 4 = 0 ⟺ 4 | p ⟺ p = 4k. p 素数 → p ≠ 4k (k ≥ 1 时 4 | p 且
p > 4 或 p = 4 非素) — 素数在 4 槽环上永不落 0 槽. -/

/-- **素数永不 ≡ 0 (mod 4)**: 素数 p ⟹ p mod 4 ≠ 0 — p mod 4 = 0
⟺ 4 | p ⟺ p = 4k (k ≥ 1) 是合数 (4·1 = 4 非素, 4k > 4 时被 4
整除) — 素数在 4 槽环 (R141) 上永不落 0 槽 — 素数 = 缺 0 槽的
实数轴子集. -/
theorem prime_mod_four_never_zero {p : ℕ} (hp : Nat.Prime p) : p % 4 ≠ 0 := by
  intro hz
  have hdiv : 4 ∣ p := Nat.dvd_of_mod_eq_zero hz
  rcases hdiv with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    norm_num at hk
    exact hp.ne_one (by omega)
  have hp_gt : 4 ≤ p := by
    have : 4 * 1 ≤ 4 * k := Nat.mul_le_mul_left 4 hkpos
    have : 4 ≤ 4 * k := by simpa using this
    omega
  have hdvd : 4 ∣ p := Nat.dvd_of_mod_eq_zero hz
  exact (Nat.Prime.not_dvd_one hp) (by
    -- 4 | p 且 4 < p 且 p 素数 → 矛盾: p 有真因子 4
    -- 用最小因子论证: 4 是 p 的真因子 (4 < p), 矛盾
    rcases hdvd with ⟨m, hm⟩
    -- p = 4*m, 4 < p, 素数 p → p = 4*m, 4*m 有因子 4
    have hmgt : 1 < m := by
      by_contra hmle
      have : m ≤ 1 := by omega
      interval_cases m
      · norm_num at hm; omega
      · norm_num at hm; omega
    have : 4 * 1 < 4 * m := Nat.mul_lt_mul_of_pos_left hmgt (by norm_num)
    have : 4 < p := by simpa [hm] using this
    omega)

/-! ## 2. ★素数像永不落 0 槽 (I^p ≠ 1)

I^p = 1 ⟺ 4 | p (I 是 4 次单位根: I^4 = 1). 素数 p 永不 ≡ 0
(mod 4) → I^p ≠ 1 — 素数在 pat (4 次单位根) 上的像 {I, -1, -I}
缺 0 槽 (+1). 素数是"少一个槽"的实数轴子集. -/

/-- **★素数像永不落 0 槽**: 素数 p ⟹ I^p ≠ 1 — I^p = 1 ⟺ 4 | p
(I 是 4 次单位根, I^4 = 1) ⟺ p = 4k (合数); 素数永不 ≡ 0 (mod 4)
(prime_mod_four_never_zero) — 素数在 pat (4 次单位根投影, R175)
上的像 {I, -1, -I} 缺 0 槽 (+1) — **pat 的 +1 位置是素数永远不
出现的位置** — 素数是缺 0 槽的实数轴子集 (映射架构图景核心). -/
theorem prime_pow_I_never_one {p : ℕ} (hp : Nat.Prime p) : Complex.I ^ p ≠ 1 := by
  intro h
  have hmod : p % 4 ≠ 0 := prime_mod_four_never_zero hp
  have hpow : Complex.I ^ (p % 4) = 1 := by
    -- I^p = I^(p % 4) · (I^4)^(p / 4) = I^(p % 4)
    have hdiv : p = p % 4 + 4 * (p / 4) := by
      omega
    rw [hdiv, pow_add, pow_mul]
    have hI4 : Complex.I ^ 4 = 1 := by norm_num
    rw [hI4]
    simp
  have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
  interval_cases h4 : p % 4 <;> norm_num at hpow ⊢
  · contradiction
  · contradiction
  · contradiction
  · contradiction

/-! ## 3. 考拉兹循环 {1, 4, 2} 的槽位 = {0, 1, 2}

1 ≡ 1, 4 ≡ 0, 2 ≡ 2 (mod 4) — 循环 (R176 collatz_cycle_142) 在
4 槽环上的槽位 = {0, 1, 2}, 永不落 3 槽. 循环相位 1 槽 → 0 槽 →
2 槽 → 1 槽, 跳过 3 槽. -/

/-- **循环 {1, 4, 2} 槽位**: 1 % 4 = 1 ∧ 4 % 4 = 0 ∧ 2 % 4 = 2 —
考拉兹循环 1 → 4 → 2 → 1 (R176 collatz_cycle_142) 在 4 槽环上的
槽位 = {0, 1, 2}: 相位 1 槽 → 0 槽 → 2 槽 → 1 槽 (永不落 3 槽) —
循环是缺 3 槽的实数轴子集. -/
theorem collatz_cycle_mod_slots :
    1 % 4 = 1 ∧ 4 % 4 = 0 ∧ 2 % 4 = 2 := by
  norm_num

/-! ## 4. ★循环像永不落 3 槽 (无 -I)

I^1 = I ≠ -I, I^4 = 1 ≠ -I, I^2 = -1 ≠ -I — 循环 {1, 4, 2} 的 pat
像 {I, 1, -1} 缺 3 槽 (-I, 虚轴负侧). 循环内部相位 1 槽 → 0 槽 →
2 槽, 永远跳过 3 槽 — 与素数缺 0 槽形成对偶. -/

/-- **★循环像永不落 3 槽**: I^1 ≠ -I ∧ I^4 ≠ -I ∧ I^2 ≠ -I — 考拉兹
循环 1 → 4 → 2 → 1 的 pat 像 {I, 1, -1} 缺 3 槽 (-I, 虚轴负侧;
R176 collatz_cycle_142; R175 4 次单位根) — 循环内部相位 1 槽 → 0
槽 → 2 槽 → 1 槽, 永远跳过 3 槽 — 与素数缺 0 槽 (prime_pow_I_
never_one) 形成对偶: 素数是缺 +1 的子集, 循环是缺 -I 的子集. -/
theorem collatz_cycle_pow_never_neg_I :
    Complex.I ^ 1 ≠ -Complex.I ∧
    Complex.I ^ 4 ≠ -Complex.I ∧
    Complex.I ^ 2 ≠ -Complex.I := by
  norm_num

/-! ## 5. 全景 — 映射架构图景

实数轴 (整数子集) → pat 4 次单位根槽位:

| 子集 | 槽位 | 缺失槽 |
|---|---|---|
| 自然数 | {0,1,2,3} | 无 |
| 素数 | {1,2,3} | **0 槽 (+1)** |
| 考拉兹循环 {1,4,2} | {0,1,2} | **3 槽 (-I)** |

每个子集都有"永远不出现"的 pat 位置 — 素数永不落 +1, 循环永不落
-I. -/

/-- **★实数轴→pat 映射架构全景**: ① 素数像永不落 0 槽 (I^p ≠ 1,
prime_pow_I_never_one: p ≡ 0 mod 4 是合数) ② 循环 {1,4,2} 槽位 =
{0,1,2} (collatz_cycle_mod_slots) ③ 循环像永不落 3 槽 (无 -I,
collatz_cycle_pow_never_neg_I) — 映射架构图景: 实数轴的不同子集
在 pat (4 次单位根, R175/R141) 上覆盖不同槽位组合, 每个子集都有
永远不出现的位置: 素数缺 0 槽 (+1), 循环缺 3 槽 (-I) — "实数轴
视角下丢失的槽" = 其子集在 pat 投影下的空缺槽位. 诚实边界: 结构
观测 (投影图景), 非素数分布理论. -/
theorem real_axis_pat_mapping_perspective {p : ℕ} (hp : Nat.Prime p) :
    (Complex.I ^ p ≠ 1) ∧
    (1 % 4 = 1 ∧ 4 % 4 = 0 ∧ 2 % 4 = 2) ∧
    (Complex.I ^ 1 ≠ -Complex.I ∧
     Complex.I ^ 4 ≠ -Complex.I ∧
     Complex.I ^ 2 ≠ -Complex.I) := by
  constructor
  · exact prime_pow_I_never_one hp
  · constructor
    · exact collatz_cycle_mod_slots
    · exact collatz_cycle_pow_never_neg_I

end PatRealAxisMapping

end ZeroRelative
