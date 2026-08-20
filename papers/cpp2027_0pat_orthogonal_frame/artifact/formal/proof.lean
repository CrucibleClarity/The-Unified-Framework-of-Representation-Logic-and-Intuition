import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic

/-!
# 习题 XXV: 正交欧拉圆坐标系 — 双模观测 (0pat)

用户洞察 (2026-08-20): 素数的轴化过程, 以两个正交的欧拉圆为坐标系进行观测。
0pat 精确化: 两个正交欧拉圆 = 互素模 p, q 的圆 ℤ/pℤ × ℤ/qℤ; 正交性 = 互素;
坐标系合成 = 中国剩余定理 (CRT): ℤ/pqℤ ≃ ℤ/pℤ × ℤ/qℤ。

- 坐标系合法性: 欧拉圆 ↔ 实数轴的映射已证 (Stereographic.lean 球极投影 /
  CircleCore.lean); 正交坐标系 = 双模投影, 合成 = CRT。
- 素数观测: 素数 p 在本征圆 ℤ/pℤ 上满足 Fermat 代数 x^p = x (习题 XXIV);
  在非本征圆 ℤ/qℤ (q ≠ p) 上投影非零, 因而是单位圆群元素: p^(q-1) ≡ 1。
- 素因子的可观测性: p | a ⟹ a 在 ℤ/pℤ 上投影为 0 (素因子在第一坐标可见)。

谱系坐标: (R23, C3) 素数圆 × 解析数论; 连接 XXIII (合数 = 素分解) 与
XXIV (素数圆 = Fermat)。无需复平面 — 纯 ℤ/nℤ 代数。
-/

namespace OrthogonalCircles

noncomputable section

open scoped BigOperators

/-- 正交坐标系合成 (CRT): 互素模 p, q 的两个正交欧拉圆的笛卡尔积
    = 合数模 pq 的圆。mathlib: ZMod.chineseRemainder。 -/
noncomputable def orthogonal_frame_crt {m n : ℕ} (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- 素因子的可观测性: 若 p | a, 则 a 在模 p 圆上的投影为 0
    (素因子在正交坐标系的第一坐标可见)。 -/
theorem factor_observable_zero {p a : ℕ} [Fact (Nat.Prime p)] (h : p ∣ a) :
    (a : ZMod p) = 0 := by
  apply ZMod.val_injective
  simp [ZMod.val_natCast, Nat.mod_eq_zero_of_dvd h]

/-- 素数的可区分性: 素数 p 在非本征圆 ℤ/qℤ (q ≠ p 素数) 上的投影非零
    (正交坐标系区分不同的素数)。 -/
theorem distinct_primes_observable {p q : ℕ} [Fact (Nat.Prime p)]
    [Fact (Nat.Prime q)] (h : p ≠ q) : (p : ZMod q) ≠ 0 := by
  have hndvd : ¬ q ∣ p := by
    intro hd
    have hcases : q = 1 ∨ q = p :=
      (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime p) q hd)
    rcases hcases with hq1 | hqp
    · exact (Nat.Prime.ne_one (Fact.out : Nat.Prime q)) hq1
    · exact h hqp.symm
  intro hz
  have hval : (p : ZMod q).val = 0 := by simp [hz]
  rw [ZMod.val_natCast] at hval
  exact hndvd (Nat.dvd_of_mod_eq_zero hval)

/-- 乘法圆群的阶: (ℤ/pℤ)ˣ 的基数是 p - 1 (p 素数)。 (习题 XXIV 复用) -/
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


/-- 素数在非本征圆上的观测: 素数 p 在 ℤ/qℤ (q ≠ p) 上是单位圆群元素,
    满足 Fermat 小定理 p^(q-1) ≡ 1 (Lagrange: 单位群阶 = q-1)。 -/
theorem prime_unit_on_other_circle {p q : ℕ} [Fact (Nat.Prime p)]
    [Fact (Nat.Prime q)] (h : p ≠ q) : p ^ (q - 1) ≡ 1 [MOD q] := by
  -- p 在 ℤ/qℤ 中非零 (distinct_primes_observable) ⟹ 与 q 互素
  have hcop : p.Coprime q := by
    have hndvd : ¬ q ∣ p := by
      intro hd
      have hcases : q = 1 ∨ q = p :=
        (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime p) q hd)
      rcases hcases with hq1 | hqp
      · exact (Nat.Prime.ne_one (Fact.out : Nat.Prime q)) hq1
      · exact h hqp.symm
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime q)).2 hndvd).symm
  -- 单位群元素 (unitOfCoprime) + Lagrange (orderOf_dvd_card + pow_orderOf_eq_one)
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime p hcop
  have horder_dvd : orderOf u ∣ Fintype.card (ZMod q)ˣ := orderOf_dvd_card
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := card_units_zmod_prime (p := q)
  have hpow : u ^ (q - 1) = 1 := by
    rcases horder_dvd with ⟨k, hk⟩
    rw [hcard] at hk
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  -- 转回 ModEq
  have hcast : (p ^ (q - 1) : ZMod q) = (1 : ZMod q) := by
    have hu : (u : ZMod q) = (p : ZMod q) := rfl
    calc
      (p ^ (q - 1) : ZMod q) = ((p : ZMod q) ^ (q - 1)) := by
        simp
      _ = (u : ZMod q) ^ (q - 1) := by rw [hu]
      _ = ((u ^ (q - 1) : (ZMod q)ˣ) : ZMod q) := by
        rw [Units.val_pow_eq_pow_val]
      _ = 1 := by rw [hpow]; rfl
  exact (ZMod.natCast_eq_natCast_iff (p ^ (q - 1)) 1 q).mp (by simpa using hcast)

end
end OrthogonalCircles
