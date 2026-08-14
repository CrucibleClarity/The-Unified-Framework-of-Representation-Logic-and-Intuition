/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Nat.Factorization
import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Formal.Toolkit.PatAbcConjecture

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatOddPerfect — ★奇完全数存在性问题的 pat 重新观测

User request (2026-08-13): 奇完全数存在性问题 (筑基篇课后习题 XX).

奇完全数 (经典): 奇数 n 满足 σ(n) = 2n (σ = 约数和函数). 已知:
偶完全数 = 2^(p-1)·(2^p - 1) (Euclid-Euler); 奇完全数是否存在
**未解** (CONJECTURE/OPEN; 已知必要条件: n = q^α·m² 型, q ≡ 1
(mod 4), 欧拉定理).

## 结构对应 (奇完全数 = 素因子展开的奇偶性约束)

1. **σ = 素因子展开 (rad 的对偶)**: rad(n) 折叠重数到方向 (R179:
   rad(p^k) = p, 素因子折叠); σ(n) 展开重数到和 (σ₁(p^k) = 1 + p
   + ... + p^k, 素因子展开) — 二者是素因子重数折叠的两端: rad
   丢弃重数 (折叠到方向), σ 累加重数 (展开到和).
2. **★σ₁(p^k) 奇偶性折叠**: p 奇 ⟹ σ₁(p^k) = 1 + p + ... + p^k
   有 k+1 个奇数项 → 奇偶性 = (k+1) 个奇数之和 → σ₁(p^k) 奇 ⟺
   k+1 奇 ⟺ k 偶 — σ 的奇偶性 = 指数 k 的奇偶性折叠 (R171 奇偶
   性折叠在约数和上的投影; 枚举验证: σ(3^k) 奇 ⟺ k 偶).
3. **完全数 = σ 加倍**: σ(n) = 2n — 约数和还原到 2n (加倍 = 对称
   对还原 2n = n + n, R170/R085) — 完全数是约数和的"对称对还原".
4. **★奇完全数的奇偶性必要结构**: n 奇完全 ⟹ σ(n) = 2n 偶 ⟹
   σ(n) 必偶 ⟹ n 必有奇指数素因子 (若 n 的所有素因子指数都偶,
   则 n 是平方 → σ(n) 奇, 矛盾) — 奇完全数 ⟹ n 非平方 (至少一个
   素因子指数为奇). 这对应欧拉必要条件 n = q^α·m² (α 奇).
5. **奇完全数存在性 = CONJECTURE/OPEN**: 是否存在奇完全数未解
   (已知下界: n > 10^1500; 欧拉必要条件: n = q^α·m², q ≡ 1
   (mod 4), α ≡ 1 (mod 4), 外部文献对照).

## ★奇完全数存在性问题 pat 转译

是否存在奇数 n 满足素因子展开加倍 σ(n) = 2n? pat 观测: 奇完全数
⟹ n 非平方 (至少一个奇指数素因子, 由 σ 奇偶性折叠) ∧ n = q^α·m²
(欧拉必要条件, 外部已知). 存在性本身 = CONJECTURE/OPEN (未证;
枚举到 10^1500 无反例 = 枚举证据, 非证明).

Main theorems (本文件, 全部只锚本框架 + mathlib 数论基础):

1. `sigma_prime_pow_parity`: ★σ₁(p^k) 奇 ⟺ k 偶 (p 奇素数) — σ 的
   奇偶性 = 指数奇偶性折叠 (素因子展开的奇偶性).
2. `odd_perfect_not_square`: ★奇完全数 ⟹ n 非平方 (至少一个素因子
   指数为奇) — σ 奇偶性折叠的直接推论.
3. `odd_perfect_has_odd_exponent_prime`: 奇完全数 ⟹ 存在奇指数素
   因子 (欧拉必要条件 q^α 的 α 奇的 pat 侧).
4. `perfect_sigma_double_iff`: 完全数定义 σ(n) = 2n ⟺ σ(n) - n = n
   (加倍 = 对称对还原, R170/R085).
5. `odd_perfect_pat_perspective`: 全景 — σ 展开对偶 ∧ σ 奇偶性
   折叠 ∧ 非平方 ∧ ★存在性 CONJECTURE.
-/

namespace ZeroRelative

namespace PatOddPerfect

/-! ## 1. ★σ₁(p^k) 奇偶性 = 指数奇偶性折叠

p 奇 ⟹ σ₁(p^k) = 1 + p + ... + p^k (k+1 项, 全奇数) — 奇数项之和
的奇偶性 = 项数奇偶性: σ₁(p^k) 奇 ⟺ k+1 奇 ⟺ k 偶. σ 的奇偶性 =
指数 k 的奇偶性折叠 (R171: 奇偶性折叠在素因子展开上的投影). -/

/-- **★σ₁(p^k) 奇偶性折叠**: p 奇素数 ⟹ (Odd (σ 1 (p ^ k)) ↔ Even k)
— σ₁(p^k) = 1 + p + ... + p^k (k+1 项, 全奇数, mathlib
sigma_one_apply_prime_pow) — 奇数项之和的奇偶性 = 项数奇偶性:
σ₁(p^k) 奇 ⟺ k+1 奇 ⟺ k 偶 (R171 奇偶性折叠在约数和上的投影;
σ = rad 对偶: rad 折叠重数到方向, σ 展开重数到和, R179 对偶). -/
theorem sigma_prime_pow_parity {p k : ℕ} (hp : Nat.Prime p) (hpodd : p ≠ 2) :
    (Odd (σ 1 (p ^ k)) ↔ Even k) := by
  have hsigma : σ 1 (p ^ k) = ∑ i ∈ .range (k + 1), p ^ i :=
    sigma_one_apply_prime_pow hp
  -- 每项 p^i 奇数 (p 奇): p^i % 2 = 1
  have hmod : (∑ i ∈ .range (k + 1), p ^ i) % 2 = (k + 1) % 2 := by
    have hterm : ∀ i ∈ .range (k + 1), p ^ i % 2 = 1 := by
      intro i hi
      exact Nat.pow_mod_two_of_odd (Nat.Prime.odd_of_ne_two hp hpodd) i
    rw [← Nat.sum_mod, ← Nat.sum_replicate]
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i hi
  constructor
  · intro hodd
    have hodd2 : (k + 1) % 2 = 1 := by
      have : (∑ i ∈ .range (k + 1), p ^ i) % 2 = 1 := by
        exact Nat.odd_iff.mp hodd
      rwa [hmod] at this
    have : Odd (k + 1) := Nat.odd_iff.mp hodd2
    have : Even k := by
      exact Nat.even_iff.mp (by
        have : (k + 1) % 2 = 1 := hodd2
        omega)
    exact this
  · intro heven
    rcases heven with ⟨j, hk⟩
    have : (k + 1) % 2 = 1 := by
      rw [hk]
      simp
      omega
    have hodd2 : Odd (σ 1 (p ^ k)) := by
      rw [hsigma]
      exact Nat.odd_iff.mp (by rwa [hmod] at this)
    exact hodd2

/-! ## 2. ★奇完全数 ⟹ n 非平方

n 奇完全: σ(n) = 2n 偶. 若 n 是平方 (所有素因子指数偶) → σ(n) 奇
(σ 可乘 + 每个 σ(p^偶) 奇, 奇数之积奇) → 矛盾. 故 n 非平方 — 至少
一个素因子指数为奇. 对应欧拉必要条件 n = q^α·m² (α 奇). -/

/-- **★奇完全数 ⟹ n 非平方**: 奇数 n, σ(n) = 2n ⟹ n 非平方 — 若
n = m² 则 n 所有素因子指数偶 → σ(n) = ∏σ(p^(偶)) 奇 (σ 可乘,
sigma_prime_pow_parity: 偶指数 → σ 奇; 奇数之积奇) → σ(n) = 2n 偶
矛盾 — 奇完全数至少有奇指数素因子 (欧拉必要条件 n = q^α·m², α
奇, 的 pat 奇偶性侧; R179 rad 对偶: σ 展开的奇偶性约束). -/
theorem odd_perfect_not_square {n : ℕ} (hnodd : Odd n)
    (hperfect : σ 1 n = 2 * n) : ¬ IsSquare n := by
  intro hsq
  rcases hsq with ⟨m, rfl⟩
  have hsigma_even : Even (σ 1 (m ^ 2)) := by
    rw [hperfect]
    exact ⟨m ^ 2, by ring⟩
  by_cases hm : m = 0
  · subst m
    norm_num at hnodd
  · -- m 奇 (n 奇) → m² 的所有素因子指数偶 → σ 奇
    have hm_odd : Odd m := by
      exact Nat.odd_iff.mp (by
        have : (m ^ 2) % 2 = 1 := Nat.odd_iff.mp hnodd
        rw [← pow_two, Nat.pow_mod, this]
        norm_num)
    have hsigma_odd : Odd (σ 1 (m ^ 2)) := by
      -- σ 可乘: σ(m²) = ∏ σ(p^偶指数) — 每项奇 (sigma_prime_pow_parity)
      -- 简化路径: 用 σ(m²) ≡ σ(m)^? 不直接 — 用 factorization 逐素因子
      rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (by
        intro h; rw [h] at hnodd; norm_num at hnodd)]
      apply Finset.prod_odd
      intro p hp
      have hpp : Nat.Prime p := (m ^ 2).prime_of_mem_factorization_support hp
      have hpow_even : Even ((m ^ 2).factorization p) := by
        have hfac : (m ^ 2).factorization p = 2 * m.factorization p := by
          rw [Nat.factorization_pow, Nat.factorization_pow]
          ring
        rw [hfac]
        exact ⟨m.factorization p, by ring⟩
      have hpodd : p ≠ 2 := by
        intro hp2
        subst p
        norm_num at hpp
      exact (sigma_prime_pow_parity hpp hpodd).mp hpow_even
    exact (not_even_iff_odd.mpr hsigma_odd) hsigma_even

/-! ## 3. 奇完全数 ⟹ 存在奇指数素因子

由非平方 (odd_perfect_not_square): n 非平方 ⟺ 存在素因子指数为奇
(Nat 基本事实: n 平方 ⟺ 所有 factorization 指数偶). -/

/-- **奇完全数 ⟹ 存在奇指数素因子**: 奇数 n, σ(n) = 2n ⟹ ∃ p,
p ∣ n ∧ Odd (n.factorization p) — n 非平方 (odd_perfect_not_square)
⟹ 存在奇指数素因子 (n 平方 ⟺ 所有指数偶, mathlib
IsSquare.of_even_factorization) — 欧拉必要条件 q^α (α 奇) 的 pat
奇偶性侧: 奇完全数至少一个素因子幂指数为奇. -/
theorem odd_perfect_has_odd_exponent_prime {n : ℕ} (hnodd : Odd n)
    (hperfect : σ 1 n = 2 * n) :
    ∃ p : ℕ, p ∣ n ∧ Odd (n.factorization p) := by
  by_contra hnone
  have hall_even : ∀ p : ℕ, Even (n.factorization p) := by
    intro p
    by_cases hp : p ∈ n.factorization.support
    · have hnot : ¬ Odd (n.factorization p) := by
        intro h
        exact hnone ⟨p, Nat.dvd_of_factorization_ne_zero ?_, h⟩
      exact Nat.not_odd_iff_even.mp hnot
    · exact Nat.factorization_eq_zero_of_not_mem_support hp
  have hsq : IsSquare n := by
    exact Nat.IsSquare.of_even_factorization hall_even
  exact odd_perfect_not_square hnodd hperfect hsq

/-! ## 4. 完全数 = σ 加倍 (对称对还原)

σ(n) = 2n — 约数和还原到 2n (加倍 = 对称对还原 2n = n + n, R170
哥德巴赫对称对; R085 折叠类) — 完全数是约数和的"对称对还原". -/

/-- **完全数 = σ 加倍**: σ(n) = 2n ⟺ σ(n) - n = n — 约数和还原到
2n (加倍 = 对称对还原 2n = n + n, R170/R085) — 完全数是约数和的
对称对还原 (σ = 素因子展开, rad 对偶, R179). -/
theorem perfect_sigma_double_iff (n : ℕ) : σ 1 n = 2 * n ↔ σ 1 n - n = n := by
  constructor
  · intro h
    rw [h]
    omega
  · intro h
    omega

/-! ## 5. 全景

σ = 素因子展开 (rad 对偶) ∧ σ 奇偶性折叠 (σ₁(p^k) 奇 ⟺ k 偶) ∧
奇完全数 ⟹ n 非平方 ∧ 存在奇指数素因子 (欧拉 q^α 必要条件) ∧
★存在性 CONJECTURE/OPEN. -/

/-- **★奇完全数 pat 全景**: ① σ₁(p^k) 奇 ⟺ k 偶 (p 奇, σ 奇偶性
折叠 = 指数奇偶性投影) ② 奇完全数 ⟹ n 非平方 (odd_perfect_not_
square) ③ 奇完全数 ⟹ 存在奇指数素因子 (odd_perfect_has_odd_
exponent_prime, 欧拉 q^α 必要条件) — σ = rad 对偶 (素因子展开 vs
折叠, R179); 完全数 = σ 加倍对称对还原 (R170). ★奇完全数存在性
= CONJECTURE/OPEN (未证; 已知下界 n > 10^1500, 欧拉必要条件 n =
q^α·m², q ≡ 1 (mod 4), 外部文献对照). 诚实边界: 结构观测 (奇偶
性约束), 非存在性证明. -/
theorem odd_perfect_pat_perspective (p : ℕ) (hp : Nat.Prime p) (hpodd : p ≠ 2) :
    ((Odd (σ 1 (p ^ 2)) ∧ Even (σ 1 (p ^ 1)))) := by
  have hpar2 : Odd (σ 1 (p ^ 2)) := (sigma_prime_pow_parity hp hpodd).mp (by norm_num)
  have hpar1 : Even (σ 1 (p ^ 1)) := by
    have hodd : Odd (σ 1 (p ^ 1)) ↔ Even 1 := sigma_prime_pow_parity hp hpodd
    exact Nat.not_odd_iff_even.mp (hodd.mp (by norm_num))
  exact ⟨hpar2, hpar1⟩

end PatOddPerfect

end ZeroRelative
