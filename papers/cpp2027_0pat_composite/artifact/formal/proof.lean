import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Basic

/-!
# 习题 XXIII: 合数 = 素数的多重投影叠加 — 0pat 证明

原 pat 习题: 合数 = 素数的多重投影叠加。
0pat 重述: **算术基本定理** — 每个大于 1 的自然数分解为素数幂之积 (存在性),
且该分解由 factorization 唯一给出 (唯一性); 合数必有非平凡素因子。

谱系坐标: (R23, C3) 素数圆 × 解析数论。
mathlib: Nat.prod_factorization_pow_eq_self, Nat.exists_prime_and_dvd。
-/

namespace CompositeProjection

open scoped BigOperators

/-- 存在性: 每个非零自然数等于其素因子分解之积。
    mathlib: Nat.prod_factorization_pow_eq_self。 -/
theorem factorization_represents {n : ℕ} (hn : n ≠ 0) :
    (n.factorization.prod fun p e => p ^ e) = n :=
  Nat.prod_factorization_pow_eq_self hn

/-- 分解的支撑只含素数: factorization 在非零指数处的基都是素数。
    mathlib: Nat.factorization_pos_iff → 指数 > 0 ⟺ 基是素数且整除。 -/
theorem factorization_support_prime {n p : ℕ} (_hn : n ≠ 0)
    (hp : p ∈ n.factorization.support) : Nat.Prime p := by
  -- support 成员 ⟺ 指数 > 0
  have hpos : 0 < n.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  -- 指数 ≠ 0; 用 factorization_eq_zero_iff 的逆否: ¬(¬素 ∨ ¬整除 ∨ n=0)
  have hnot0 : n.factorization p ≠ 0 := by omega
  -- 若 p 非素, 由 factorization_eq_zero_iff 得 f p = 0, 矛盾
  by_contra hnp
  apply hnot0
  exact (Nat.factorization_eq_zero_iff n p).mpr (Or.inl hnp)

/-- 唯一性: 任何素支撑分解若乘积等于 n, 则等于 n.factorization。
    (即: factorization 是唯一的分解函数 — 由 Finsupp 相等 + 支撑素性唯一确定。) -/
theorem factorization_unique {n : ℕ} (hn : n ≠ 0) {f : ℕ →₀ ℕ}
    (hf : f.prod (fun p e => p ^ e) = n)
    (hfs : ∀ p, p ∈ f.support → Nat.Prime p) :
    f = n.factorization := by
  -- 唯一性由 mathlib 的唯一分解等价给出: Nat.factorizationEquiv : ℕ+ ≃ {f | 素支撑}
  -- 1. 逆映射把 f 送到 n: (symm ⟨f, hfs⟩) = f.prod (·^·) = n
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hsymm : (Nat.factorizationEquiv.symm ⟨f, hfs⟩ : ℕ) = n := by
    change (Nat.factorizationEquiv.symm ⟨f, hfs⟩).1 = n
    rw [Nat.factorizationEquiv_symm_apply_coe]
    exact hf
  -- 2. symm 单射 ⟹ ⟨f, hfs⟩ = factorizationEquiv n
  have hsymm' : Nat.factorizationEquiv.symm ⟨f, hfs⟩ = ⟨n, hnpos⟩ := by
    apply Subtype.ext
    exact hsymm
  have hfeq : ⟨f, hfs⟩ = Nat.factorizationEquiv ⟨n, hnpos⟩ := by
    exact (Equiv.symm_apply_eq Nat.factorizationEquiv).mp hsymm'
  -- 3+4. 组合 ⟹ f = n.factorization
  have hfin : (⟨f, hfs⟩ : {g : ℕ →₀ ℕ // ∀ p, p ∈ g.support → Nat.Prime p}) =
      (⟨n.factorization, by intro p hp; exact factorization_support_prime hn hp⟩ : {g : ℕ →₀ ℕ // ∀ p, p ∈ g.support → Nat.Prime p}) := by
    rw [hfeq]
    -- factorizationEquiv ⟨n,hnpos⟩ 定义性等于 ⟨n.factorization, _⟩ (mathlib match)
    apply Subtype.ext
    change (Nat.factorizationEquiv (⟨n, hnpos⟩ : ℕ+)).1 = n.factorization
    rw [Nat.factorizationEquiv_apply]
  exact congrArg Subtype.val hfin

/-- 合数必有非平凡素因子: n > 1 且非素 ⟹ ∃ p 素数, p ∣ n 且 p < n。 -/
theorem composite_has_prime_factor {n : ℕ} (hn1 : 1 < n) (hnc : ¬ Nat.Prime n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p < n := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  refine ⟨p, hp, hpd, ?_⟩
  by_contra hnot
  have hn_le_p : n ≤ p := le_of_not_gt hnot
  have hp_le_n : p ≤ n := Nat.le_of_dvd (by omega : 0 < n) hpd
  have hpn : p = n := le_antisymm hp_le_n hn_le_p
  have : Nat.Prime n := by simpa [hpn] using hp
  exact hnc this

end CompositeProjection
