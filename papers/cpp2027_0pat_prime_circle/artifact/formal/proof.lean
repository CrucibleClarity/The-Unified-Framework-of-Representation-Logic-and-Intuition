import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# 习题 XXIV: 周期圆上的素数 — 素数轴周期化 (0pat)

用户洞察 (2026-08-20): 素数轴周期化后, 在欧拉圆视角下素数轴本身也是个圆。
0pat 精确化: 自然数轴模 p 蜷曲成圆 ℤ/pℤ; 素数的圆结构由乘法圆群 (ℤ/pℤ)ˣ 承载:
- 圆的特征: Fermat 小定理 — 素数 p 在圆 ℤ/pℤ 上满足 x^p = x (ZMod.pow_card 的代数内核)
- 乘法圆群的阶: (ℤ/pℤ)ˣ 的阶 = p - 1 (非零元素全部可逆)
- Lagrange: 圆群中每个元素 a^(p-1) = 1 (欧拉定理的素数情形)
- 无穷多素数 (素数在数轴上的整体结构, mathlib: exists_infinite_primes)

谱系坐标: (R23, C3) 素数圆 × 解析数论; 无需复平面 — 纯 ℤ/pℤ 代数。
-/

namespace PrimeCircle

noncomputable section

open scoped BigOperators

/-- 乘法圆群的阶: (ℤ/pℤ)ˣ 的基数是 p - 1 (p 素数)。
    证明: (ZMod p)ˣ ≃ {x : ZMod p // x.val.Coprime p} (mathlib);
    后者 = {x : ZMod p // x ≠ 0} (p 素时互素 ⟺ 非零), card = p - 1。 -/
theorem card_units_zmod_prime {p : ℕ} [Fact (Nat.Prime p)] :
    Fintype.card (ZMod p)ˣ = p - 1 := by
  -- 1. units ≃ {x : ZMod p // x.val.Coprime p} (mathlib)
  have he : (ZMod p)ˣ ≃ {x : ZMod p // x.val.Coprime p} :=
    ZMod.unitsEquivCoprime (n := p)
  -- 2. 引理: 1 ≤ m < p (p 素) ⟹ m.Coprime p (mathlib: coprime_iff_not_dvd)
  have hprime_cop : ∀ {m : ℕ}, 1 ≤ m → m < p → m.Coprime p := by
    intro m hm1 hmp
    -- m.Coprime p ⟺ p.Coprime m (对称) ⟺ ¬ p ∣ m (素数); p ∤ m 因 m < p 且 m > 0
    have hpm : p.Coprime m :=
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 (by
        intro hpdvd
        have hpm_le : p ≤ m := Nat.le_of_dvd hm1 hpdvd
        omega)
    exact hpm.symm
  -- 3. 互素 ⟺ 非零 (p 素)
  have hcoprime_iff : ∀ x : ZMod p, x.val.Coprime p ↔ x ≠ 0 := by
    intro x
    constructor
    · intro hcop hx0
      have hval0 : x.val = 0 := by simp [hx0]
      have : ¬ (0 : ℕ).Coprime p := by
        intro h
        have : p = 1 := by simpa [Nat.Coprime] using h
        exact (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).ne' this
      exact this (by simpa [hval0] using hcop)
    · intro hx0
      have hv0 : x.val ≠ 0 := (ZMod.val_ne_zero x).2 hx0
      exact hprime_cop (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)) (ZMod.val_lt x)
  -- 4. {x // Coprime} ≃ {x // x ≠ 0}
  have hsub : {x : ZMod p // x.val.Coprime p} ≃ {x : ZMod p // x ≠ 0} := by
    refine Equiv.ofBijective (fun x => ⟨x.1, (hcoprime_iff x.1).1 x.2⟩) ?_
    constructor
    · intro a b h
      exact Subtype.ext (by simpa using (congrArg Subtype.val h))
    · intro y
      refine ⟨⟨y.1, (hcoprime_iff y.1).2 y.2⟩, ?_⟩
      rfl
  -- 5. {x : ZMod p // x ≠ 0} ≃ Fin (p - 1): x ↦ x.val - 1, k ↦ (k+1)
  have hne : {x : ZMod p // x ≠ 0} ≃ Fin (p - 1) := by
    refine Equiv.ofBijective
      (fun x => ⟨x.1.val - 1, by
        have hv0 : x.1.val ≠ 0 := (ZMod.val_ne_zero x.1).2 x.2
        have hvlt : x.1.val < p := ZMod.val_lt x.1
        omega⟩)
      ?_
    constructor
    · intro a b h
      apply Subtype.ext
      -- ↑(a.val - 1 + 1) = a (natCast_zmod_val)
      have hva : ((a.1.val - 1 + 1 : ℕ) : ZMod p) = a.1 := by
        have hsub : a.1.val - 1 + 1 = a.1.val := by
          have hv0 : a.1.val ≠ 0 := (ZMod.val_ne_zero a.1).2 a.2
          have h1 : 1 ≤ a.1.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
          rw [Nat.sub_add_cancel h1]
        rw [hsub]
        exact ZMod.natCast_zmod_val a.1
      have hvb : ((b.1.val - 1 + 1 : ℕ) : ZMod p) = b.1 := by
        have hsub : b.1.val - 1 + 1 = b.1.val := by
          have hv0 : b.1.val ≠ 0 := (ZMod.val_ne_zero b.1).2 b.2
          have h1 : 1 ≤ b.1.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
          rw [Nat.sub_add_cancel h1]
        rw [hsub]
        exact ZMod.natCast_zmod_val b.1
      have hk : a.1.val - 1 = b.1.val - 1 := by
        have hf := congrArg Fin.val h
        simpa using hf
      have : a.1.val = b.1.val := by
        have h1a : 1 ≤ a.1.val := by
          have hv0 : a.1.val ≠ 0 := (ZMod.val_ne_zero a.1).2 a.2
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
        have h1b : 1 ≤ b.1.val := by
          have hv0 : b.1.val ≠ 0 := (ZMod.val_ne_zero b.1).2 b.2
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
        omega
      exact (ZMod.val_injective p) this
    · intro k
      refine ⟨⟨((k.1 + 1 : ℕ) : ZMod p), ?_⟩, ?_⟩
      · -- (k+1) ≠ 0: (k+1).val = k+1 > 0
        have hklt : k.1 + 1 < p := by
          have : k.1 < p - 1 := k.2
          omega
        have hval : ((k.1 + 1 : ℕ) : ZMod p).val = k.1 + 1 := by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt hklt
        intro h
        have : k.1 + 1 = 0 := by
          have hc := congrArg ZMod.val h
          -- hc : ((k.1 + 1 : ℕ) : ZMod p).val = 0
          rw [hval] at hc
          simp at hc
        omega
      · apply Fin.ext
        have hklt : k.1 + 1 < p := by
          have : k.1 < p - 1 := k.2
          omega
        have hval : ((k.1 + 1 : ℕ) : ZMod p).val = k.1 + 1 := by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt hklt
        -- 目标: ((k.1 + 1 : ℕ) : ZMod p).val - 1 = k.1
        dsimp
        rw [hval]
        change k.1 + 1 - 1 = k.1
        omega
  -- 6. 组合: card = p - 1
  calc
    Fintype.card (ZMod p)ˣ = Fintype.card {x : ZMod p // x.val.Coprime p} := Fintype.card_congr he
    _ = Fintype.card {x : ZMod p // x ≠ 0} := Fintype.card_congr hsub
    _ = Fintype.card (Fin (p - 1)) := Fintype.card_congr hne
    _ = p - 1 := by simp

/-- Fermat 小定理 (欧拉圆上的素数): a 与 p 互素 ⟹ a^(p-1) ≡ 1 [MOD p]。
    证明: a 在乘法圆群 (ℤ/pℤ)ˣ 中; 圆群阶 = p-1; Lagrange ⟹ a^(p-1) = 1。 -/
theorem fermat_little {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ} (hpa : a.Coprime p) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  -- a mod p 是圆群元素
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime a hpa
  -- u 的阶整除圆群阶
  have horder_dvd : orderOf u ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := card_units_zmod_prime
  -- u^orderOf = 1, orderOf | p-1 ⟹ u^(p-1) = 1
  have hpow : u ^ (p - 1) = 1 := by
    rcases horder_dvd with ⟨k, hk⟩
    rw [hcard] at hk
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  -- 转回 ModEq: u = (a : ZMod p), 1 = (1 : ZMod p)
  have hcast : (a ^ (p - 1) : ZMod p) = (1 : ZMod p) := by
    have hu : (u : ZMod p) = (a : ZMod p) := rfl
    calc
      (a ^ (p - 1) : ZMod p) = ((a : ZMod p) ^ (p - 1)) := by
        simp
      _ = (u : ZMod p) ^ (p - 1) := by rw [hu]
      _ = ((u ^ (p - 1) : (ZMod p)ˣ) : ZMod p) := by
        rw [Units.val_pow_eq_pow_val]
      _ = 1 := by rw [hpow]; rfl
  exact (ZMod.natCast_eq_natCast_iff (a ^ (p - 1)) 1 p).mp (by simpa using hcast)

/-- Fermat 小定理的完整形式: 任意 a (含 p 整除 a 的情形): a^p ≡ a [MOD p]。 -/
theorem fermat_little_complete {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ) :
    a ^ p ≡ a [MOD p] := by
  by_cases hpa : a.Coprime p
  · -- 互素情形: a^(p-1) = 1 ⟹ a^p = a
    have h := fermat_little (p := p) (a := a) hpa
    -- a^p = a^(p-1) * a ≡ 1 * a = a
    have hp : p = p - 1 + 1 := by
      have hp0 : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
      omega
    have hpow_eq : a ^ p = a ^ (p - 1) * a := by
      have hpa' : a ^ (p - 1 + 1) = a ^ (p - 1) * a := by
        rw [pow_succ]
      rw [← hp] at hpa'
      exact hpa'
    have hmod : a ^ p ≡ 1 * a [MOD p] := by
      rw [hpow_eq]
      exact Nat.ModEq.mul_right a h
    -- 1 * a = a, 替换进 ModEq
    have h1a : 1 * a = a := by omega
    have hmod' : a ^ p ≡ a [MOD p] := by
      -- hmod : a^p ≡ 1*a; 1*a = a — 等式替换进 ModEq
      rw [h1a] at hmod
      exact hmod
    exact hmod'
  · -- 不互素情形: p 素 ⟹ p | a ⟹ 两边 ≡ 0
    have hpdvd : p ∣ a := by
      -- 素数与 a 不互素 ⟹ p | a (mathlib: coprime_iff_not_dvd 的逆否)
      by_contra hnotdvd
      apply hpa
      -- p 素且 p ∤ a ⟹ a.Coprime p (对称 + coprime_iff_not_dvd)
      have hpc : p.Coprime a :=
        (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hnotdvd
      exact hpc.symm
    -- p | a ⟹ a ≡ 0; ModEq.pow 提升: a^p ≡ 0^p = 0; 两边同余 0
    have ha0 : a ≡ 0 [MOD p] := by
      simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd hpdvd]
    have hmod0 : a ^ p ≡ 0 [MOD p] := by
      simpa [Nat.Prime.ne_zero (Fact.out : Nat.Prime p)] using ha0.pow p
    exact hmod0.trans ha0.symm

/-- 无穷多素数 (数轴上的素数整体结构, mathlib)。 -/
theorem infinitely_many_primes (n : ℕ) : ∃ p : ℕ, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes n

end
