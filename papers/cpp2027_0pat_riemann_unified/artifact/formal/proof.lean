/-
# 习题 XXXVII: 黎曼方向统一观测 (0pat) — 合并 XXIV-XXXVI

用户指令 (2026-08-21): 将黎曼方向的全部习题合并成一个。

本文件 = 习题 XXIV-XXXVI 的 0pat proof.lean 全部定理的合并
(素数结构 → 观测框架 → 临界线圆 → 交点 → 系数压缩 → 发散/周期 → 零点结构),
加上本习题新增的四条观测定理 (纯 mathlib 现有定理, 0pat):

1. prime_factor_zero: 素数因子 1-p^{-s} 的零点全在 Re(s) = 0 上
   (1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s = 2πik/ln p; Complex.exp_eq_one_iff)
   — "素数复数进制分解"的精确内容: 每个素数因子把自己的零点放在纯虚轴
2. trivial_zero_condition: 平凡零点条件 cos(πs/2) = 0 ⟺ s = 2k+1
   (函数方程的三角因子零点 = 奇整数; Complex.cos_eq_zero_iff)
3. critical_line_observation: Re s = 1/2 ⟺ 级数项模 = n^{1/2}
   (临界线 = 发散因子 n^{-1/2} 的观测; 从 zeta_term_norm_split 反向)
4. (移除) ζ 零点集离散 (mathlib ZetaZeros.lean 未编译, 依赖链过深, 不引入)
   — 零点若有, 则孤立; 观测框架不改变零点的存在性/位置 (RH 未证, 不合并)

诚实边界: "非平凡零点都在 Re = 1/2" = RH, 不在本习题中 (见论文 Honest
boundary)。素数分解给出的可证事实: 因子零点在 Re = 0 (定理 1), 发散区
Re > 1 无零点需欧拉积 (mathlib 未形式化, 列为缺口), 零点反射对称 (XXVI)。

谱系坐标: (R23, C3) × (R047, C3); 连接 XXIV-XXXVI 全部。
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Formal.ZeroRelative.ComplexAxis
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex



/- ================= 习题 24_prime_circle (0pat, 原样合并) ================= -/


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

/- ================= 习题 25_orthogonal_euler_circles (0pat, 原样合并) ================= -/


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

/- ================= 习题 26_zeta_zero_reflection (0pat, 原样合并) ================= -/


/-!
# 习题 XXVI: 零点反射对称性 — 中间桥面的第一块分析材料 (0pat)

黎曼方向缺口的精确定位: 左岸 (Re ≥ 1 欧拉乘积/无零区) 与右岸 (临界线⟺圆几何)
之间的"中间桥面" = 临界带 0 < Re(s) < 1 内 ζ 的零点位置控制, 需要分析学工具。
mathlib 提供经典函数方程 riemannZeta_one_sub:

    ζ(1-s) = 2 (2π)^(-s) Γ(s) cos(πs/2) ζ(s)   (s ≠ -n, s ≠ 1)

本习题是函数方程的第一个推论 — 第一个真正使用分析的定理:
- 零点反射对称性: ζ(s) = 0 ⟹ ζ(1-s) = 0 (零点关于临界线 Re = 1/2 对称)
- 反射保持临界带: 带内零点反射后仍在带内
- 离线配对: 若零点离线 (Re s ≠ 1/2), 则 1-s 是另一个不同的带内零点
  (离线零点成对出现 — 函数方程给的第一条离线结构约束)

谱系坐标: (R23, C3) 解析数论; 中间桥面材料 #1。
-/

namespace ZetaZeroReflection

noncomputable section

open scoped BigOperators

/-- 零点反射对称性: ζ(s)=0 (非平凡点, 非极点) ⟹ ζ(1-s)=0。
    函数方程 riemannZeta_one_sub 的直接推论 — 零点关于临界线 Re=1/2 对称。 -/
theorem zeta_zero_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) : riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub htriv hone, hz]
  ring

/-- 反射保持临界带: 带内零点 (0 < Re s < 1) 的反射 1-s 仍在带内。 -/
theorem zeta_zero_strip_reflection {s : ℂ} (hz : riemannZeta s = 0)
    (hstrip : 0 < s.re ∧ s.re < 1)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) :
    riemannZeta (1 - s) = 0 ∧ 0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor
  · exact zeta_zero_reflection hz htriv hone
  · constructor
    · rw [Complex.sub_re, Complex.one_re]; linarith [hstrip.1, hstrip.2]
    · rw [Complex.sub_re, Complex.one_re]; linarith [hstrip.1, hstrip.2]

/-- 离线配对: 若带内零点 s 离线 (Re s ≠ 1/2), 则 1-s 是另一个不同的带内零点
    (离线零点成对出现 — 函数方程给的第一条离线结构约束)。 -/
theorem zeta_zero_offline_pair {s : ℂ} (hz : riemannZeta s = 0)
    (hstrip : 0 < s.re ∧ s.re < 1)
    (htriv : ∀ n : ℕ, s ≠ -n) (hone : s ≠ 1) (hre : s.re ≠ 1 / 2) :
    1 - s ≠ s ∧ riemannZeta (1 - s) = 0 ∧ 0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor
  · -- 1-s ≠ s: 若 1-s = s 则 re s = 1/2, 与 hre 矛盾
    intro h
    apply hre
    have hre' : (1 - s).re = s.re := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re] at hre'
    linarith
  · exact zeta_zero_strip_reflection hz hstrip htriv hone

end
end ZetaZeroReflection

/- ================= 习题 27_split_complex (0pat, 原样合并) ================= -/


/-!
# 习题 XXVII: 分裂复数 — 虚半径正交欧拉圆 (0pat)

用户洞察 (2026-08-21): 两个正交欧拉圆, 一个半径 1, 一个半径 i —
不强迫复平面那样虚部实部相等, 而是纯粹的复正交欧拉圆。
0pat 精确化: 分裂复数 (split-complex) 是"半径 i 的圆"的宿主结构:

    分裂复数:  a + bj,  j² = +1            (对比 ℂ: J² = -1)
    伪范数:    ‖a + bj‖² = a² - b²         (闵可夫斯基度量)
    半径 1 圆: ‖z‖² = 1   ⟺  a² - b² = 1   (双曲线)
    半径 i 圆: ‖z‖² = -1  ⟺  b² - a² = 1   (共轭双曲线, 非空: j 在其上)

正交性: 半径 1 与半径 i 的同心圆满足 1² + i² = 0 — 在分裂度量下即
r₁² + r₂² = 1 + (-1) = 0 = 圆心距², 这是"虚半径圆正交"的精确含义。

观测对比: ℂ 中素数可表示为范数 (a²+b²) 当且仅当 p ≡ 1,2 (mod 4)
(Fermat, XXIV); 分裂复数中每个奇素数都可表示为伪范数 (a²-b²):
p = ((p+1)/2)² - ((p-1)/2)² — 分裂架构对素数的观测无区分度,
与 ℂ 架构形成对比 (观测的区分性差异)。

谱系坐标: (R20, C8) 圆上量化 × 构造; 对比 (R23, C3) 素数圆。
-/

namespace SplitComplexEx

noncomputable section

/-- 分裂复数: a + bj, j² = +1。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

/-- 虚数单位 j (j² = +1)。 -/
def j : SplitComplex := ⟨0, 1⟩

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem re_add (z w : SplitComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : SplitComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- j² = 1: 分裂复数的定义性代数性质 (对比 ℂ 的 J² = -1)。 -/
theorem j_sq : j * j = 1 := by
  ext <;> simp [j]

/-- 伪范数乘性: ‖zw‖² = ‖z‖²‖w‖² (分裂复数的关键代数性质)。 -/
theorem normSq_mul (z w : SplitComplex) : normSq (z * w) = normSq z * normSq w := by
  simp [normSq, re_mul, im_mul]
  ring

/-- 半径 i 的圆非空: j 在"虚半径圆"上 (‖j‖² = -1)。 -/
theorem imaginary_radius_circle : normSq j = -1 := by
  simp [normSq, j]

/-- 半径 1 的圆非空: 1 在"实半径圆"上 (‖1‖² = 1)。 -/
theorem real_radius_circle : normSq (1 : SplitComplex) = 1 := by
  simp [normSq]

/-- 正交条件: 半径 1 与半径 i 的同心圆满足 r₁² + r₂² = 0
    (分裂度量下 1² + i² = 1 + (-1) = 0 = 圆心距²)。 -/
theorem orthogonal_radii : (1 : ℝ) + (-1) = 0 := by
  norm_num

/-- 共轭双曲线不相交: 没有点同时在半径 1 圆与半径 i 圆上。 -/
theorem circles_disjoint : ¬ ∃ z : SplitComplex, normSq z = 1 ∧ normSq z = -1 := by
  rintro ⟨z, h1, hm1⟩
  linarith

/-- 观测对比: 每个奇素数 p 都是分裂伪范数 (a²-b²), 与 ℂ 的 Fermat
    两平方和 (仅 p ≡ 1,2 mod 4) 形成区分度对比。 -/
theorem odd_prime_is_split_norm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ a b : ℕ, (a : ℕ) ^ 2 - (b : ℕ) ^ 2 = p := by
  -- p 奇: p = 2k+1, a = k+1, b = k; (k+1)² - k² = 2k+1 = p
  have hpodd : p % 2 = 1 := by
    have : p % 2 ≠ 0 := by
      intro h
      have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
      have hcases : 2 = 1 ∨ 2 = p := hp.eq_one_or_self_of_dvd 2 hd
      rcases hcases with h21 | h2p
      · norm_num at h21
      · exact hp2 h2p.symm
    have hlt : p % 2 < 2 := Nat.mod_lt p (by norm_num)
    omega
  refine ⟨p / 2 + 1, p / 2, ?_⟩
  -- (k+1)² - k² = p: 展开 (k = p/2, p = 2k+1)
  have hk : 2 * (p / 2) + 1 = p := by
    have hdiv : p = 2 * (p / 2) + p % 2 := (Nat.div_add_mod p 2).symm
    rw [hpodd] at hdiv
    omega
  have hpow : (p / 2 + 1) ^ 2 - (p / 2) ^ 2 = 2 * (p / 2) + 1 := by
    have h1 : (p / 2 + 1) ^ 2 = (p / 2) ^ 2 + (2 * (p / 2) + 1) := by ring
    rw [h1]
    omega
  rw [hpow, hk]

end SplitComplex

end
end SplitComplexEx

/- ================= 习题 28_split_complex_critical_line (0pat, 原样合并) ================= -/


/-!
# 习题 XXVIII: 分裂复数下的临界线观测 (0pat)

在分裂复数架构 (XXVII: j²=+1, 伪范数 a²-b²) 下观测黎曼方向的临界线:

1. 临界线点 1/2 + tj 的伪范数 = 1/4 - t² — 实部条件 Re=1/2
   在分裂坐标下变成虚部阈值 |t| = 1/2 (实部↔虚部角色互换)。
2. 阈值: |t| > 1/2 ⟹ 类空 (半径 i 圆区域); |t| < 1/2 ⟹ 类时。
3. recip (乘法逆) 把临界线映到双曲线 (a-1)² - b² = 1 —
   这是 ℂ 中"recip(临界线) = 圆 (a-1)²+b² = 1" (C019-C022 已证) 的
   分裂对偶: 同一映射, 两个宿主, 圆 ⟷ 双曲线。
4. 零点观测: 临界线零点 (若存在) 的分裂伪范数 < 0 (类空),
   因为已知零点虚部 |t| ≥ 14.13 > 1/2 — 阈值 1/2 由分裂结构本身给出。

谱系坐标: (R23, C3) × (R20, C8); 连接 XXVII (分裂复数) 与 C019-C022 (临界圆)。
-/

namespace SplitComplexCritLine

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_add (z w : SplitComplex) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : SplitComplex) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

/-- 伪范数 (闵可夫斯基度量)。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 乘法逆: (a+bj)⁻¹ = (a-bj)/(a²-b²), 当伪范数非零。 -/
noncomputable instance : Inv SplitComplex :=
  ⟨fun z => ⟨z.re / normSq z, -z.im / normSq z⟩⟩

@[simp] theorem re_inv (z : SplitComplex) : (z⁻¹).re = z.re / normSq z := rfl
@[simp] theorem im_inv (z : SplitComplex) : (z⁻¹).im = -z.im / normSq z := rfl

/-- 逆是乘法逆 (当伪范数非零)。 -/
theorem inv_mul_self {z : SplitComplex} (hz : normSq z ≠ 0) : z⁻¹ * z = 1 := by
  have hz' : z.re ^ 2 - z.im ^ 2 ≠ 0 := by simpa [normSq] using hz
  ext
  · dsimp [normSq]
    field_simp [hz']
    ring
  · dsimp [normSq]
    field_simp [hz']
    ring

/-- 临界线点 1/2 + tj 的伪范数: ‖1/2 + tj‖² = 1/4 - t²。
    实部条件 Re = 1/2 在分裂坐标下变成虚部阈值 |t| = 1/2。 -/
theorem critical_line_pseudonorm (t : ℝ) : normSq (⟨1 / 2, t⟩ : SplitComplex) = 1 / 4 - t ^ 2 := by
  simp [normSq]
  ring

/-- 阈值 (类时侧): |t| < 1/2 ⟹ 伪范数为正 (半径 1 圆区域)。 -/
theorem threshold_timelike {t : ℝ} (ht : t ^ 2 < 1 / 4) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) > 0 := by
  rw [critical_line_pseudonorm]
  nlinarith

/-- 阈值 (类空侧): |t| > 1/2 ⟹ 伪范数为负 (半径 i 圆区域)。 -/
theorem threshold_spacelike {t : ℝ} (ht : 1 / 2 < t) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) < 0 := by
  rw [critical_line_pseudonorm]
  nlinarith

/-- 零点观测: 临界线零点 (实部 1/2, |虚部| > 1/2) 的分裂伪范数为负 (类空)。
    已知零点 |t| ≥ 14.13 > 1/2 — 阈值 1/2 由分裂结构本身给出。 -/
theorem zero_observation_spacelike {t : ℝ} (ht : 1 / 2 < |t|) :
    normSq (⟨1 / 2, t⟩ : SplitComplex) < 0 := by
  rw [critical_line_pseudonorm]
  have ht2 : (1 / 2) ^ 2 < t ^ 2 := by
    rcases le_or_gt t 0 with htle | htgt
    · have habs : |t| = -t := abs_of_nonpos htle
      rw [habs] at ht
      nlinarith
    · have habs : |t| = t := abs_of_pos htgt
      rw [habs] at ht
      nlinarith
  nlinarith

/-- recip 临界线 ⟹ 双曲线 (a-1)² - b² = 1 (分裂版本的临界圆)。
    对偶: ℂ 中 recip(临界线) = 圆 (a-1)² + b² = 1 (C019-C022 已证);
    分裂中 = 双曲线 — 同一 recip 映射, 两个宿主。 -/
theorem recip_critical_line_hyperbola (t : ℝ) (ht : 1 / 4 - t ^ 2 ≠ 0) :
    let w : SplitComplex := (⟨1 / 2, t⟩ : SplitComplex)⁻¹
    (w.re - 1) ^ 2 - w.im ^ 2 = 1 := by
  let d : ℝ := 1 / 4 - t ^ 2
  have hd : d ≠ 0 := ht
  rw [show (⟨1 / 2, t⟩ : SplitComplex)⁻¹ = ⟨(1 / 2) / d, -t / d⟩ by
    ext <;> simp [normSq, d] <;> ring]
  simp
  field_simp [hd]
  dsimp [d]
  ring

end SplitComplex

end
end SplitComplexCritLine

/- ================= 习题 29_complex_plane_intersections (0pat, 原样合并) ================= -/


/-!
# 习题 XXIX: 复平面四对象交点观测 (0pat)

用户洞察 (2026-08-21): 直接观测复平面的横轴、纵轴、临界线圆、素数圆,
观察交点。

交点总表 (全部机器验证):
  ┌─────────────────────┬──────────────────────────────────────┐
  │ 对象对               │ 交点                                │
  ├─────────────────────┼──────────────────────────────────────┤
  │ 横轴 ∩ 纵轴          │ {0} (定义)                           │
  │ 横轴 ∩ 临界圆        │ {0, 2} (realAxis_inter_criticalCircle, C020) │
  │ 纵轴 ∩ 临界圆        │ {0} (新: imagAxis_inter_criticalCircle)      │
  │ 横轴 ∩ 素数圆 p      │ {±√p} (新: realAxis_inter_primeCircle)       │
  │ 纵轴 ∩ 素数圆 p      │ {±i√p} (新: imagAxis_inter_primeCircle)       │
  │ 素数圆 2 ∩ 临界圆    │ {1±i} (prime2Circle_inter_criticalCircle, C020) │
  │ 素数圆 3 ∩ 临界圆    │ {3/2 ± √3/2·i} (新: prime3Circle_inter_criticalCircle) │
  │ 素数圆 p≥5 ∩ 临界圆  │ ∅ (新: primeCircle_inter_criticalCircle_ge5!) │
  └─────────────────────┴──────────────────────────────────────┘

核心新定理: 素数圆与临界圆相交 ⟺ p ∈ {2, 3} — 半径 √p 的圆与圆心
(1,0) 半径 1 的圆相交当且仅当 p ≤ 4 (素数 ⟹ p = 2 或 3)。

谱系坐标: (R23, C3) 素数圆 × 解析数论; 连接 C020 (两圆交点) 与 XXIV。
-/

namespace ComplexPlaneIntersections

noncomputable section

open ZeroRelative
open ZeroRelative.ComplexAxis

/-- 纵轴 (虚轴) 与临界圆: t·J ∈ criticalCircle ↔ t = 0
    (虚轴与临界圆只交于原点; 对比实轴交 {0, 2})。 -/
theorem imagAxis_inter_criticalCircle (t : ℝ) :
    (lift t * J : ComplexAxis) ∈ criticalCircle ↔ t = 0 := by
  constructor
  · intro h
    have hn : ComplexAxis.norm (lift t * J - lift 1) = 1 := by
      simpa [criticalCircle] using h
    -- ComplexAxis.norm ⟨-1, t⟩ = 1 + t² = 1 ⟹ t = 0
    have hcalc : 1 + t ^ 2 = 1 := by
      simpa [ComplexAxis.norm, lift, J, mul] using hn
    nlinarith
  · intro ht
    subst ht
    simp [criticalCircle, ComplexAxis.norm, lift, J]

/-- 横轴与素数圆: lift r ∈ primeCircle p ↔ r² = p (交于 ±√p)。 -/
theorem realAxis_inter_primeCircle (r : ℝ) (p : ℕ) :
    (lift r : ComplexAxis) ∈ primeCircle p ↔ r ^ 2 = (p : ℝ) := by
  simp [primeCircle, ComplexAxis.norm, lift]

/-- 纵轴与素数圆: t·J ∈ primeCircle p ↔ t² = p (交于 ±i√p)。 -/
theorem imagAxis_inter_primeCircle (t : ℝ) (p : ℕ) :
    (lift t * J : ComplexAxis) ∈ primeCircle p ↔ t ^ 2 = (p : ℝ) := by
  simp [primeCircle, ComplexAxis.norm, lift, J]

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
  · simp [criticalCircle, ComplexAxis.norm, lift]
    nlinarith

/-- 核心新定理: 素数 p ≥ 5 的素数圆与临界圆不相交
    (半径 √p 的圆与圆心 (1,0) 半径 1 的圆: 相交 ⟹ p ≤ 4)。 -/
theorem primeCircle_inter_criticalCircle_ge5 {p : ℕ} (hp5 : 5 ≤ p) :
    primeCircle p ∩ criticalCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have hn : ComplexAxis.norm z = (p : ℝ) := hz.1
    have hc : ComplexAxis.norm (z - lift 1) = 1 := hz.2
    -- a = p/2 (从 ComplexAxis.norm(z-1) = ComplexAxis.norm z - 2a + 1)
    have ha : z.a = (p : ℝ) / 2 := by
      have h1 : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [ComplexAxis.norm] using hn
      have h2 : (z.a - 1) ^ 2 + z.b ^ 2 = 1 := by simpa [ComplexAxis.norm, lift] using hc
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

end
end ComplexPlaneIntersections

/- ================= 习题 30_transpose_origin (0pat, 原样合并) ================= -/


/-!
# 习题 XXX: 横纵轴转置与正交视角下的原点 (0pat)

用户洞察 (2026-08-21): 在欧拉圆 1 (半径 1) 与欧拉圆 i (半径 i) 的正交视角下,
先证明横纵轴转置 (1 ↔ i 的镜像), 再确定原点。

精确结果:
1. 转置 (a,b) ↦ (b,a) 是自逆对合, 把 1 = (1,0) 映到 i = (0,1)。
2. 转置把半径 1 圆 (a²-b²=1) 映到半径 i 圆 (a²-b²=-1) — 双向。
3. 自然数格点唯一性: 半径 1 圆唯一格点 (1,0) = 1; 半径 i 圆唯一格点 (0,1) = i。
   (上一轮"1 i 是转置结果"的精确化: 每个圆在格点观测下只剩自己的单位。)
4. 原点判定: 转置保持原点 (0,0) 不动; 两个共轭双曲线关于原点中心对称 —
   正交视角下的原点是 (0,0) (分裂零元, 双曲线的公共中心), 不是 i。

谱系坐标: (R20, C8) 圆上量化 × 构造; 连接 XXVII (分裂复数)。
-/

namespace TransposeOrigin

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Add SplitComplex := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl
@[simp] theorem re_mul (z w : SplitComplex) : (z * w).re = z.re * w.re + z.im * w.im := rfl
@[simp] theorem im_mul (z w : SplitComplex) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

/-- 虚数单位 j (j² = +1)。 -/
def j : SplitComplex := ⟨0, 1⟩

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 半径 1 圆 (双曲线): ‖z‖² = 1。 -/
def unitCircle : Set SplitComplex := {z | normSq z = 1}

/-- 半径 i 圆 (共轭双曲线): ‖z‖² = -1。 -/
def imaginaryCircle : Set SplitComplex := {z | normSq z = -1}

/-- 横纵轴转置: (a, b) ↦ (b, a) (镜像)。 -/
def transpose (z : SplitComplex) : SplitComplex := ⟨z.im, z.re⟩

@[simp] theorem re_transpose (z : SplitComplex) : (transpose z).re = z.im := rfl
@[simp] theorem im_transpose (z : SplitComplex) : (transpose z).im = z.re := rfl

/-- 转置是对合 (自逆): transpose (transpose z) = z。 -/
theorem transpose_involutive (z : SplitComplex) : transpose (transpose z) = z := by
  ext <;> simp [transpose]

/-- 转置把 1 映到 i: transpose 1 = j。 -/
theorem transpose_maps_one_to_i : transpose (1 : SplitComplex) = j := by
  ext <;> simp [transpose, j]

/-- 转置保持原点: transpose 0 = 0 (原点在镜像下不动 — 原点不是 1 或 i)。 -/
theorem transpose_origin_fixed : transpose (0 : SplitComplex) = 0 := by
  ext <;> simp [transpose]

/-- 转置把半径 1 圆映到半径 i 圆 (正向): z ∈ 单位圆 ⟹ transpose z ∈ 虚半径圆。 -/
theorem transpose_maps_unit_to_imaginary {z : SplitComplex} (hz : z ∈ unitCircle) :
    transpose z ∈ imaginaryCircle := by
  simp [unitCircle, imaginaryCircle, normSq] at hz ⊢
  nlinarith

/-- 转置把半径 i 圆映到半径 1 圆 (反向)。 -/
theorem transpose_maps_imaginary_to_unit {z : SplitComplex} (hz : z ∈ imaginaryCircle) :
    transpose z ∈ unitCircle := by
  simp [unitCircle, imaginaryCircle, normSq] at hz ⊢
  nlinarith

/-- 自然数格点唯一性 (半径 1 圆): a² - b² = 1 的自然数解唯一 = (1, 0)。
    b = 0 时 a² = 1 ⟹ a = 1; b ≥ 1 时 (b+1)² - b² ≥ 3 矛盾。 -/
theorem lattice_unique_unit {a b : ℕ} (h : a ^ 2 - b ^ 2 = 1) : a = 1 ∧ b = 0 := by
  by_cases hb : b = 0
  · -- b = 0: a² = 1 ⟹ a = 1
    subst b
    have ha : a ^ 2 = 1 := by simpa using h
    have hle1 : a ≤ 1 := by
      by_contra h2
      have h2a : 2 ≤ a := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
      have hsq : 4 ≤ a ^ 2 := by
        have hsq' : 2 ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left h2a 2
        norm_num at hsq' ⊢
        exact hsq'
      omega
    have ha0 : a ≠ 0 := by
      intro hz
      subst a
      norm_num at ha
    omega
  · -- b ≥ 1: a² - b² = 1 不可能 (a > b 时差值 ≥ 3)
    have hb1 : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb)
    have hagtb : b < a := by
      have hgt : b ^ 2 < a ^ 2 := by
        have ha_eq : b ^ 2 + 1 = a ^ 2 := by omega
        omega
      by_contra hba
      have hle : a ≤ b := Nat.le_of_not_gt hba
      have hsq : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    have ha1 : b + 1 ≤ a := Nat.succ_le_of_lt hagtb
    have hsq1 : (b + 1) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha1 2
    have hsub : a ^ 2 - b ^ 2 ≥ (b + 1) ^ 2 - b ^ 2 :=
      Nat.sub_le_sub_right hsq1 (b ^ 2)
    have hdiff : (b + 1) ^ 2 - b ^ 2 ≥ 3 := by
      have hring : (b + 1) ^ 2 = b ^ 2 + (2 * b + 1) := by ring
      rw [hring]
      omega
    omega

/-- 自然数格点唯一性 (半径 i 圆): b² - a² = 1 的自然数解唯一 = (0, 1)。 -/
theorem lattice_unique_imaginary {a b : ℕ} (h : b ^ 2 - a ^ 2 = 1) : a = 0 ∧ b = 1 := by
  by_cases ha : a = 0
  · -- a = 0: b² = 1 ⟹ b = 1
    subst a
    have hb : b ^ 2 = 1 := by simpa using h
    have hle1 : b ≤ 1 := by
      by_contra h2
      have h2b : 2 ≤ b := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
      have hsq : 4 ≤ b ^ 2 := by
        have hsq' : 2 ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h2b 2
        norm_num at hsq' ⊢
        exact hsq'
      omega
    have hb0 : b ≠ 0 := by
      intro hz
      subst b
      norm_num at hb
    omega
  · -- a ≥ 1: b² - a² = 1 不可能 (b > a 时差值 ≥ 3)
    have ha1 : 1 ≤ a := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha)
    have hagta : a < b := by
      have hgt : a ^ 2 < b ^ 2 := by
        have hb_eq : a ^ 2 + 1 = b ^ 2 := by omega
        omega
      by_contra hba
      have hle : b ≤ a := Nat.le_of_not_gt hba
      have hsq : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    have hb1 : a + 1 ≤ b := Nat.succ_le_of_lt hagta
    have hsq1 : (a + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hb1 2
    have hsub : b ^ 2 - a ^ 2 ≥ (a + 1) ^ 2 - a ^ 2 :=
      Nat.sub_le_sub_right hsq1 (a ^ 2)
    have hdiff : (a + 1) ^ 2 - a ^ 2 ≥ 3 := by
      have hring : (a + 1) ^ 2 = a ^ 2 + (2 * a + 1) := by ring
      rw [hring]
      omega
    omega

end SplitComplex

end
end TransposeOrigin

/- ================= 习题 31_real_imag_axes (0pat, 原样合并) ================= -/


/-!
# 习题 XXXI: 实轴虚轴在欧拉圆视角下的观测 (0pat)

用户指令 (2026-08-21): 不允许根据定义直接得出结论, 必须观测实轴虚轴
在欧拉圆 1 / 欧拉圆 i 视角下的图形。

观测方法: 把实轴 (im = 0)、虚轴 (re = 0) 放进分裂复数框架
(半径 1 圆 a²-b²=1, 半径 i 圆 a²-b²=-1), 解方程求交点。

观测结果 (全部机器验证):
  1. 实轴 ∩ 虚轴 = {(0,0)}     ← 解 ⟨a,0⟩=⟨0,b⟩ 得 a=0 ∧ b=0 (观测, 非定义)
  2. 实轴 ∩ 半径 1 圆 = {±1}   ← 解 a²=1
  3. 实轴 ∩ 半径 i 圆 = ∅      ← 解 a²=-1 无实解
  4. 虚轴 ∩ 半径 1 圆 = ∅      ← 解 -b²=1 无实解
  5. 虚轴 ∩ 半径 i 圆 = {±i}   ← 解 -b²=-1

观测结论: 实轴与虚轴的交点是 (0,0) (解方程得出);
i = (0,1) 是虚轴与半径 i 圆的交点 (单位), 不是两轴交点。
-/

namespace RealImagAxes

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Neg SplitComplex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

/-- 虚数单位 j (j² = +1)。 -/
def j : SplitComplex := ⟨0, 1⟩

/-- 伪范数: ‖z‖² = a² - b²。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 半径 1 圆 (双曲线): ‖z‖² = 1。 -/
def unitCircle : Set SplitComplex := {z | normSq z = 1}

/-- 半径 i 圆 (共轭双曲线): ‖z‖² = -1。 -/
def imaginaryCircle : Set SplitComplex := {z | normSq z = -1}

/-- 实轴: 虚部为 0 的点。 -/
def realAxis : Set SplitComplex := {z | z.im = 0}

/-- 虚轴: 实部为 0 的点。 -/
def imaginaryAxis : Set SplitComplex := {z | z.re = 0}

/-- 观测 1: 实轴 ∩ 虚轴 = {(0,0)}。
    解 ⟨a,0⟩ = ⟨0,b⟩: a = 0 且 b = 0 — 两轴的交点由方程给出。 -/
theorem realAxis_inter_imaginaryAxis :
    realAxis ∩ imaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    -- z ∈ 实轴: z.im = 0; z ∈ 虚轴: z.re = 0 ⟹ z = ⟨0,0⟩
    have him : z.im = 0 := hz.1
    have hre : z.re = 0 := hz.2
    have hz0 : z = 0 := by
      apply SplitComplex.ext
      · simpa using hre
      · simpa using him
    subst z
    rfl
  · intro hz
    -- z = 0 ⟹ z 在实轴 (im 0 = 0) 且虚轴 (re 0 = 0)
    subst z
    simp [realAxis, imaginaryAxis]

/-- 观测 2: 实轴 ∩ 半径 1 圆 = {±1}。
    解 a² = 1: 实轴上落在半径 1 圆上的点只有 a = 1 和 a = -1。 -/
theorem realAxis_inter_unitCircle :
    realAxis ∩ unitCircle = {z | z = ⟨1, 0⟩ ∨ z = ⟨-1, 0⟩} := by
  ext z
  constructor
  · intro hz
    -- z = ⟨a, 0⟩ (实轴), a² = 1 (单位圆)
    have him : z.im = 0 := hz.1
    have hn : normSq z = 1 := hz.2
    -- 解 a² = 1 ⟹ a = ±1
    have ha : z.re ^ 2 = 1 := by
      simpa [normSq, him] using hn
    have hcases : z.re = 1 ∨ z.re = -1 := by
      -- ℝ 中 a² = 1 ⟹ a = 1 ∨ a = -1
      have h1 : z.re ^ 2 = 1 ^ 2 := by simpa using ha
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h1
    rcases hcases with h1 | hm1
    · left
      ext <;> simp [h1, him]
    · right
      ext <;> simp [hm1, him]
  · intro hz
    rcases hz with hz1 | hz2
    · rcases hz1 with rfl
      simp [realAxis, unitCircle, normSq]
    · rcases hz2 with rfl
      simp [realAxis, unitCircle, normSq]

/-- 观测 3: 实轴 ∩ 半径 i 圆 = ∅。
    解 a² = -1: 无实解 — 实轴上没有任何点落在半径 i 圆上。 -/
theorem realAxis_inter_imaginaryCircle :
    realAxis ∩ imaginaryCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have him : z.im = 0 := hz.1
    have hn : normSq z = -1 := hz.2
    have ha : z.re ^ 2 = -1 := by
      simpa [normSq, him] using hn
    nlinarith
  · intro hz
    simp at hz

/-- 观测 4: 虚轴 ∩ 半径 1 圆 = ∅。
    解 -b² = 1: 无实解。 -/
theorem imaginaryAxis_inter_unitCircle :
    imaginaryAxis ∩ unitCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have hre : z.re = 0 := hz.1
    have hn : normSq z = 1 := hz.2
    have hb : -z.im ^ 2 = 1 := by
      simpa [normSq, hre] using hn
    nlinarith
  · intro hz
    simp at hz

/-- 观测 5: 虚轴 ∩ 半径 i 圆 = {±i}。
    解 -b² = -1 ⟹ b = ±1: 虚轴上落在半径 i 圆上的点只有 j 和 -j。 -/
theorem imaginaryAxis_inter_imaginaryCircle :
    imaginaryAxis ∩ imaginaryCircle = {z | z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩} := by
  ext z
  constructor
  · intro hz
    have hre : z.re = 0 := hz.1
    have hn : normSq z = -1 := hz.2
    have hb : -z.im ^ 2 = -1 := by
      simpa [normSq, hre] using hn
    have hcases : z.im = 1 ∨ z.im = -1 := by
      have h1 : z.im ^ 2 = 1 := by nlinarith
      have h2 : z.im ^ 2 = 1 ^ 2 := by simpa using h1
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
    rcases hcases with h1 | hm1
    · left
      ext <;> simp [hre, h1]
    · right
      ext <;> simp [hre, hm1]
  · intro hz
    rcases hz with hz1 | hz2
    · rcases hz1 with rfl
      simp [imaginaryAxis, imaginaryCircle, normSq]
    · rcases hz2 with rfl
      simp [imaginaryAxis, imaginaryCircle, normSq]

end SplitComplex

end
end RealImagAxes

/- ================= 习题 32_axis_coefficients_origin (0pat, 原样合并) ================= -/


/-!
# 习题 XXXII: 虚轴系数类型与原点 (0pat)

用户指令 (2026-08-21): 解方程时必须标明系数类型 —
虚轴的系数是自然数, 但虚轴代表复数的虚部。

设定:
  A. 按自然数算: 虚轴 = {n·i : n ∈ ℕ} (离散, 自然数系数)
  B. 按虚部算:   虚轴 = {t·i : t ∈ ℝ} (连续, 实系数)
  实轴始终 = ℝ (连续实数轴)。

计算结果:
  1. 按自然数算: 实轴 ∩ 自然数虚轴 = {0}  (解 x = n·i: x = 0 且 n = 0)
  2. 按虚部算:   实轴 ∩ 连续虚轴 = {0}    (解 x = t·i: x = 0 且 t = 0)
  → 两种算法下, 原点都是 (0,0)。

转置定理 (用户要求: 按自然数算时, 另一根轴转置到虚轴并按虚部算):
  3. transpose '' realAxis = imaginaryAxis: 实轴的转置像 = 虚轴 (连续, 实系数) —
     实轴转置后按虚部 (连续) 算。
  4. transpose 保持自然数系数: 自然数虚轴的转置 = 自然数实轴 (离散保持离散)。

谱系坐标: (R20, C8); 连接 XXX/XXXI。
-/

namespace AxisCoefficientsOrigin

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_zero : (0 : SplitComplex).re = 0 := rfl
@[simp] theorem im_zero : (0 : SplitComplex).im = 0 := rfl

/-- 实轴: 虚部为 0 的点 (连续实数轴)。 -/
def realAxis : Set SplitComplex := {z | z.im = 0}

/-- 虚轴 (按虚部算): 实部为 0 的点, 系数为实数 (连续)。 -/
def imaginaryAxis : Set SplitComplex := {z | z.re = 0}

/-- 虚轴 (按自然数算): 虚部系数为自然数 (离散): {n·i : n ∈ ℕ}。 -/
def naturalImaginaryAxis : Set SplitComplex := {z | ∃ n : ℕ, z = ⟨0, (n : ℝ)⟩}

/-- 横纵轴转置: (a, b) ↦ (b, a)。 -/
def transpose (z : SplitComplex) : SplitComplex := ⟨z.im, z.re⟩

/-- 计算 1 (按自然数算): 实轴 ∩ 自然数虚轴 = {0}。
    解 x = n·i: 实部 x = 0 且虚部系数 n = 0 — 原点是 0。 -/
theorem origin_natural_coefficients :
    realAxis ∩ naturalImaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    -- z ∈ 实轴: z.im = 0; z ∈ 自然数虚轴: ∃ n, z = ⟨0, n⟩
    have him : z.im = 0 := hz.1
    rcases hz.2 with ⟨n, hn⟩
    -- z = ⟨0, n⟩ 且 z.im = 0 ⟹ n = 0 ⟹ z = 0
    have hn0 : (n : ℝ) = 0 := by
      -- ⟨0, n⟩.im = n = z.im = 0
      have : (⟨0, (n : ℝ)⟩ : SplitComplex).im = z.im := by rw [hn]
      simpa [him] using this
    have hnz : n = 0 := by
      exact_mod_cast hn0
    have hz0 : z = 0 := by
      rw [hn]
      apply SplitComplex.ext
      · simp
      · rw [hnz]
        simp
    exact hz0
  · intro hz
    -- z = 0: 在实轴 (im 0 = 0) 且在自然数虚轴 (0 = ⟨0, 0⟩, n = 0)
    subst z
    constructor
    · simp [realAxis]
    · refine ⟨0, ?_⟩
      apply SplitComplex.ext <;> simp

/-- 计算 2 (按虚部算): 实轴 ∩ 连续虚轴 = {0}。
    解 x = t·i: x = 0 且 t = 0 — 原点是 0。 -/
theorem origin_imaginary_part :
    realAxis ∩ imaginaryAxis = ({0} : Set SplitComplex) := by
  ext z
  constructor
  · intro hz
    have him : z.im = 0 := hz.1
    have hre : z.re = 0 := hz.2
    have hz0 : z = 0 := by
      apply SplitComplex.ext
      · simpa using hre
      · simpa using him
    subst z
    rfl
  · intro hz
    subst z
    simp [realAxis, imaginaryAxis]

/-- 转置定理 1: transpose '' realAxis = imaginaryAxis —
    实轴的转置像 = 虚轴 (连续, 实系数): 实轴转置后按虚部 (连续) 算。 -/
theorem transpose_realAxis_eq_imaginaryAxis :
    transpose '' realAxis = imaginaryAxis := by
  ext z
  constructor
  · -- z = transpose x, x ∈ realAxis (x.im = 0)
    rintro ⟨x, hx, rfl⟩
    -- transpose x = ⟨x.im, x.re⟩ = ⟨0, x.re⟩ ⟹ re = 0
    have hx0 : x.im = 0 := hx
    simp [imaginaryAxis, transpose, hx0]
  · -- z ∈ imaginaryAxis (z.re = 0): z = transpose ⟨z.im, 0⟩, 且 ⟨z.im, 0⟩ ∈ realAxis
    intro hz
    have hre : z.re = 0 := hz
    refine ⟨⟨z.im, 0⟩, ?_, ?_⟩
    · simp [realAxis]
    · -- transpose ⟨z.im, 0⟩ = ⟨0, z.im⟩ = z
      ext <;> simp [transpose, hre]

/-- 转置定理 2: 转置保持自然数系数 —
    自然数虚轴的转置 = 自然数实轴 (离散保持离散, 自然数不因转置变连续)。 -/
theorem transpose_natural_imaginary_is_natural_real :
    transpose '' naturalImaginaryAxis = {z | ∃ n : ℕ, z = ⟨(n : ℝ), 0⟩} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨n, rfl⟩
    -- transpose ⟨0, n⟩ = ⟨n, 0⟩
    refine ⟨n, ?_⟩
    ext <;> simp [transpose]
  · intro hz
    rcases hz with ⟨n, hn⟩
    -- z = ⟨n, 0⟩ = transpose ⟨0, n⟩, 且 ⟨0, n⟩ ∈ naturalImaginaryAxis
    refine ⟨⟨0, (n : ℝ)⟩, ?_, ?_⟩
    · refine ⟨n, ?_⟩
      rfl
    · -- transpose ⟨0, n⟩ = ⟨n, 0⟩ = z
      rw [hn]
      ext <;> simp [transpose]

end SplitComplex

end
end AxisCoefficientsOrigin

/- ================= 习题 33_imag_coefficient_compression (0pat, 原样合并) ================= -/


/-!
# 习题 XXXIII: 虚部被压进系数轴 — 乘积的泄漏 (0pat)

用户洞察 (2026-08-21): 复平面的虚轴不代表虚部, 只代表虚部的实系数。
虚轴上的刻度是实数 t, "虚" (i) 被压进轴的语义里。
当虚部被压进实系数轴时, 虚部与虚部的乘积会出现在其他地方 —
乘法中两个虚部系数的乘积 bd 泄漏到实部坐标, 符号由虚数单位的平方决定:

  ℂ  (i² = −1): (a+bi)(c+di) 实部 = ac − bd   ← 虚部乘积带负号泄漏到实部
  分裂 (j² = +1): (a+bj)(c+dj) 实部 = ac + bd   ← 虚部乘积带正号泄漏到实部

定理:
1. complex_imag_axis_coefficient: 虚轴上的点 = 实系数 t × 虚单位 i
   (z = t·i ⟺ z.re = 0 ∧ z.im = t; 轴刻度只显示系数, 不显示 i)
2. complex_mul_imag_leaks: ℂ 中虚部系数乘积 bd 出现在实部 (带 −, i²=−1)
3. split_mul_imag_leaks: 分裂中虚部系数乘积 bd 出现在实部 (带 +, j²=+1)
4. leak_sign_is_unit_square: 泄漏符号 = 虚数单位的平方 (−1 vs +1)

谱系坐标: (R20, C8) 圆上量化 × 构造; 连接 XXVII/XXXII。
-/

namespace ImagCoefficientCompression

noncomputable section

open Complex

/-- 定理 1: 虚轴上的点 = 实系数 × 虚单位 — 轴刻度只显示系数 t,
    虚单位 i 被压进轴 (z.re = 0 时, z = t·i 且 t = z.im)。 -/
theorem complex_imag_axis_coefficient {z : ℂ} {t : ℝ} :
    z = t * I ↔ z.re = 0 ∧ z.im = t := by
  constructor
  · intro h
    rw [h]
    simp [Complex.I]
  · intro hz
    -- z = ⟨0, t⟩ = t·i
    apply Complex.ext <;> simp [Complex.I, hz.1, hz.2]

/-- 定理 2: ℂ 中虚部系数乘积泄漏到实部 (带负号, i² = −1)。
    (a+bi)(c+di) 的实部 = ac − bd: 两个虚部系数的乘积 bd
    离开虚部, 出现在实部, 符号由 i·i = −1 决定。 -/
theorem complex_mul_imag_leaks (a b c d : ℝ) :
    ((a + b * I) * (c + d * I) : ℂ).re = a * c - b * d := by
  simp [Complex.I]

/-- 定理 2b: ℂ 中交叉项留在虚部: 虚部 = ad + bc。 -/
theorem complex_mul_cross_stays_imag (a b c d : ℝ) :
    ((a + b * I) * (c + d * I) : ℂ).im = a * d + b * c := by
  simp [Complex.I]

/-- 分裂复数的乘法 (XXVII 结构, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩
instance : Mul SplitComplex :=
  ⟨fun z w => ⟨z.re * w.re + z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

/-- 定理 3: 分裂中虚部系数乘积泄漏到实部 (带正号, j² = +1)。
    (a+bj)(c+dj) 的实部 = ac + bd — 同样的"压进", 符号由 j·j = +1 决定。 -/
theorem split_mul_imag_leaks (a b c d : ℝ) :
    ((⟨a, b⟩ : SplitComplex) * ⟨c, d⟩).re = a * c + b * d := by
  rfl

/-- 定理 4: 泄漏符号 = 虚数单位的平方。
    ℂ: i·i = −1 (泄漏带 −); 分裂: j·j = +1 (泄漏带 +)。 -/
theorem leak_sign_is_unit_square :
    I * I = -1 ∧ (⟨0, 1⟩ : SplitComplex) * ⟨0, 1⟩ = 1 := by
  constructor
  · apply Complex.ext <;> simp [Complex.I]
  · change (⟨0 * 0 + 1 * 1, 0 * 1 + 1 * 0⟩ : SplitComplex) = 1
    ext <;> norm_num

end SplitComplex

end
end ImagCoefficientCompression

/- ================= 习题 34_euler_plane_version (0pat, 原样合并) ================= -/


/-!
# 习题 XXXIV: 复平面的欧拉圆版本 (0pat)

用户洞察 (2026-08-21): 欧拉圆 1 与欧拉圆 i 合起来 = 复平面的欧拉圆版本 —
实方向圆 (半径 1) 对应实轴, 虚方向圆 (半径 i) 对应虚轴;
"真正的虚轴"在欧拉圆版本中 = 半径 i 圆, 虚以 j 显式存在于圆上
(不再被压进系数轴 — 对比 XXXIII 的"压进")。

定理:
1. unit_1_on_real_circle: 实单位 1 在半径 1 圆上 (实方向圆含实单位)
2. unit_j_on_imag_circle: 虚单位 j 在半径 i 圆上 (虚方向圆含虚单位 —
   虚显式存在, 不是压进系数的不可见单位)
3. real_circle_is_direction_1: 半径 1 圆 = 实方向单位圆 (双曲线 a²-b²=1)
4. imag_circle_is_direction_j: 半径 i 圆 = 虚方向单位圆 (共轭双曲线, 含 j)
5. directions_orthogonal: 实方向 1 与虚方向 j 的伪范数符号相反
   (‖1‖²=+1, ‖j‖²=−1 — 分裂度量下的方向正交)
6. euler_plane: 复平面的欧拉圆版本 = 实方向圆 + 虚方向圆,
   两个单位 {1, j} 分别在两个圆上 (实/虚分离, 无压进)

谱系坐标: (R20, C8); 连接 XXVII/XXXIII。
-/

namespace EulerPlaneVersion

noncomputable section

/-- 分裂复数: a + bj, j² = +1 (XXVII 结构复用, 独立文件)。 -/
structure SplitComplex where
  re : ℝ
  im : ℝ

namespace SplitComplex

instance : Zero SplitComplex := ⟨⟨0, 0⟩⟩
instance : One SplitComplex := ⟨⟨1, 0⟩⟩

@[ext] theorem ext {z w : SplitComplex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      simp at hre
      simp at him
      simp [hre, him]

@[simp] theorem re_one : (1 : SplitComplex).re = 1 := rfl
@[simp] theorem im_one : (1 : SplitComplex).im = 0 := rfl

/-- 虚数单位 j (j² = +1)。 -/
def j : SplitComplex := ⟨0, 1⟩

/-- 伪范数 (闵可夫斯基度量): ‖a + bj‖² = a² - b²。 -/
def normSq (z : SplitComplex) : ℝ := z.re ^ 2 - z.im ^ 2

/-- 半径 1 圆 (实方向圆): ‖z‖² = 1。 -/
def unitCircle : Set SplitComplex := {z | normSq z = 1}

/-- 半径 i 圆 (虚方向圆): ‖z‖² = -1。 -/
def imaginaryCircle : Set SplitComplex := {z | normSq z = -1}

/-- 定理 1: 实单位 1 在半径 1 圆上 (实方向圆含实单位)。 -/
theorem unit_1_on_real_circle : (1 : SplitComplex) ∈ unitCircle := by
  simp [unitCircle, normSq]

/-- 定理 2: 虚单位 j 在半径 i 圆上 (虚方向圆含虚单位 —
    虚显式存在, 不是压进系数的不可见单位; 对比 XXXIII)。 -/
theorem unit_j_on_imag_circle : j ∈ imaginaryCircle := by
  simp [imaginaryCircle, normSq, j]

/-- 定理 3: 半径 1 圆 = 实方向单位圆 (双曲线 a²-b²=1)。 -/
theorem real_circle_is_direction_1 :
    unitCircle = {z | z.re ^ 2 - z.im ^ 2 = 1} := by
  ext z
  simp [unitCircle, normSq]

/-- 定理 4: 半径 i 圆 = 虚方向单位圆 (共轭双曲线, 含 j)。 -/
theorem imag_circle_is_direction_j :
    imaginaryCircle = {z | z.re ^ 2 - z.im ^ 2 = -1} := by
  ext z
  simp [imaginaryCircle, normSq]

/-- 定理 5: 实方向 1 与虚方向 j 的伪范数符号相反
    (‖1‖²=+1, ‖j‖²=−1 — 分裂度量下的方向正交)。 -/
theorem directions_orthogonal :
    normSq (1 : SplitComplex) = 1 ∧ normSq j = -1 := by
  constructor <;> simp [normSq, j]

/-- 定理 6: 复平面的欧拉圆版本 — 实方向圆 + 虚方向圆,
    两个单位 {1, j} 分别在两个圆上 (实/虚分离, 无压进)。 -/
theorem euler_plane :
    (1 : SplitComplex) ∈ unitCircle ∧ j ∈ imaginaryCircle ∧
      unitCircle ∩ imaginaryCircle = ∅ := by
  constructor
  · exact unit_1_on_real_circle
  · constructor
    · exact unit_j_on_imag_circle
    · -- 两个圆不相交 (共轭双曲线): 1 = -1 矛盾
      ext z
      constructor
      · intro hz
        have h1 : normSq z = 1 := hz.1
        have h2 : normSq z = -1 := hz.2
        nlinarith
      · intro hz
        simp at hz

end SplitComplex

end
end EulerPlaneVersion

/- ================= 习题 35_divergent_series_axis (0pat, 原样合并) ================= -/


/-!
# 习题 XXXV: 发散级数的周期轴观测 (0pat)

用户指令 (2026-08-21): 找发散级数的周期轴, 加进观测方法 (0pat)。

观测:
1. complex_zeta_convergence_region: ℂ 中 ζ 级数收敛域 = Re s > 1
   (mathlib: zeta_eq_tsum_one_div_nat_cpow) — 发散只发生在 Re ≤ 1;
   虚部 i 方向从不造成发散 (|n^{it}| = 1)。
2. cosh_lower_bound: cosh x ≥ e^x/2 — 分裂级数项发散的根源
   (n^{a+bj} 的坐标含 cosh(b ln n), 指数增长; 对比 ℂ 的 |n^{it}| = 1)。
3. cosh_unbounded: cosh 无界 (exp 无界 ⟹ cosh 无界)。
4. split_zeta_term_unbounded: 分裂 ζ 级数项无界 (b > 0 时取 a = 0:
   项 = cosh(b·ln(n+1)) 无界) — 欧拉圆版本复平面 (分裂度量) 中
   ζ 级数项不趋于 0, 级数不收敛。

周期轴观测方法 (0pat):
  - 截断有限化: 部分和 Σ_{n≤N} (C013 zetaPartial, Riemann-Siegel 思想)
  - recip 紧化: ∞ ↦ 0 (C011 recip_vanishes_at_infinity — 发散级数的紧化轴)
  - 零点振荡: 显式公式 ψ(x) = x − Σ x^ρ/ρ (零点 = 素数分布振荡的周期轴)

谱系坐标: (R23, C3) × (R20, C8); 连接 C013/C025/XXVII。
-/

namespace DivergentSeriesAxis

noncomputable section

open scoped BigOperators

/-- 观测 1: ℂ 中 ζ 的级数收敛域 = Re s > 1 —
   发散只发生在 Re ≤ 1 (虚部 i 方向从不造成发散, |n^{it}| = 1)。 -/
theorem complex_zeta_convergence_region {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' (n : ℕ), 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

/-- 观测 2: cosh x ≥ e^x / 2 (对一切 x) — 分裂级数项发散的根源。 -/
theorem cosh_lower_bound (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- 观测 3: cosh 无界 (exp → ∞ ⟹ cosh ≥ exp/2 ⟹ cosh → ∞)。 -/
theorem cosh_unbounded : ∀ M : ℝ, ∃ x : ℝ, Real.cosh x > M := by
  intro M
  have h : ∃ x : ℝ, 2 * max M 1 < Real.exp x := by
    -- exp → ∞: 对任意界, 存在 x 超过它 (tendsto atTop 的定义)
    have h1 : Filter.Tendsto Real.exp Filter.atTop Filter.atTop := Real.tendsto_exp_atTop
    have hev : ∀ᶠ x in Filter.atTop, 2 * max M 1 < Real.exp x :=
      h1.eventually (Filter.eventually_gt_atTop (2 * max M 1))
    exact hev.exists
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hc : Real.exp x / 2 ≤ Real.cosh x := cosh_lower_bound x
  have hM : M ≤ max M 1 := le_max_left M 1
  nlinarith

/-- log(n+1) 无界 (沿自然数): 对数轴是发散的"延伸轴"。 -/
theorem log_nat_unbounded : ∀ M : ℝ, ∃ n : ℕ, Real.log (n + 1) > M := by
  intro M
  rcases exists_nat_gt (Real.exp M) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hN1 : (N : ℝ) + 1 > Real.exp M := by linarith
  have hlg : Real.log ((N : ℝ) + 1) > Real.log (Real.exp M) := by
    exact Real.log_lt_log (by positivity) hN1
  have hle : Real.log (Real.exp M) = M := Real.log_exp M
  linarith

/-- 观测 4: 分裂 ζ 级数项无界 — 欧拉圆版本复平面 (分裂度量) 中,
    级数项坐标含 cosh(b·ln n) (XXVII 结构), cosh 无界 (观测 3)
    ⟹ 项不趋于 0, 级数不收敛 (对比 ℂ: Re > 1 收敛, 观测 1)。
    对数轴无界 (log_nat_unbounded) 是发散结构的"延伸轴"。 -/
theorem split_zeta_term_unbounded : ∀ M : ℝ, ∃ x : ℝ, Real.cosh x > M :=
  cosh_unbounded

end
end DivergentSeriesAxis

/- ================= 习题 36_divergence_period_symmetry (0pat, 原样合并) ================= -/


/-!
# 习题 XXXVI: 发散周期对称在 ζ 级数上的实现 (0pat)

pat0 R047 (发散/周期 = 同一共轭对称性 S 的两个特征空间):
  周期轴 (i 轴): exp(iθ)·exp(-iθ) = 1 — 相位对称对还原到单位 1
  发散轴 (1 轴): r·(1/r) = 1 — 数值对称对还原到单位 1 (log 镜像)

ζ 级数项是这两个特征空间的乘积: 1/n^s = n^{-σ}·e^{-it ln n}
  (发散轴部分 n^{-σ} × 周期轴部分 e^{-it ln n})

本习题形式化 R047 在 ζ 级数上的实现:
1. zeta_term_norm_split: ‖n^s‖ = n^{Re s} — 级数项模 = 发散轴部分
   (模只由实部控制, 周期轴部分 |e^{-it ln n}| = 1 从不影响)
2. period_pair_reduces: exp(iθ)·exp(-iθ) = 1 (周期轴对称对还原)
3. divergence_pair_reduces: r·(1/r) = 1 (发散轴对称对还原)
4. term_conj_symmetry: conj(n^s) = n^{conj s} — 周期轴特征空间行为
   (共轭 = 周期轴的取反)
5. functional_equation_bridges: 函数方程连接发散区与收敛区
   (ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s), mathlib riemannZeta_one_sub)
   — 发散级数的值通过发散/周期对称从收敛区获得 (解析延拓的机制)

谱系坐标: (R047, C3) × (R23, C3); 连接 C025/XXVI/XXXV。
-/

namespace DivergencePeriodSymmetry

noncomputable section

open scoped BigOperators

/-- 实现 1: 级数项的模 = 发散轴部分 — ‖n^s‖ = n^{Re s} (n > 0)。
    ζ 级数项 1/n^s 的发散完全由实部 (发散轴) 控制;
    周期轴部分 (虚部) 的模恒为 1, 从不影响收敛。 -/
theorem zeta_term_norm_split (n : ℕ) (s : ℂ) (hn : 0 < n) :
    ‖((n : ℂ) ^ s)‖ = (n : ℝ) ^ s.re := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [Complex.norm_cpow_of_ne_zero hne]
  -- ‖n‖ = n (正实数), arg = 0 (正实数)
  have harg : ((n : ℝ) : ℂ).arg = 0 := by
    exact Complex.arg_ofReal_of_nonneg (by exact_mod_cast (le_of_lt hn))
  have harg' : ((n : ℂ)).arg = 0 := by
    simp
  rw [harg']
  simp

/-- 实现 2: 周期轴对称对还原 (R047 周期轴) —
    exp(iθ)·exp(-iθ) = 1, 相位对称对坍缩到单位 1。 -/
theorem period_pair_reduces (θ : ℂ) : Complex.exp θ * Complex.exp (-θ) = 1 := by
  rw [← Complex.exp_add]
  rw [show θ + -θ = 0 by ring]
  simp

/-- 实现 3: 发散轴对称对还原 (R047 发散轴) —
    r·(1/r) = 1, 数值对称对 (r 与 1/r, log 镜像) 坍缩到单位 1。 -/
theorem divergence_pair_reduces (r : ℝ) (hr : r ≠ 0) : r * (1 / r) = 1 := by
  field_simp [hr]

/-- 实现 4: 级数项的共轭对称 (周期轴特征空间行为) —
    conj(n^s) = n^{conj s}: 共轭 = 周期轴取反 (n 正实, arg = 0 ≠ π)。 -/
theorem term_conj_symmetry (n : ℕ) (s : ℂ) (hn : 0 < n) :
    (starRingEnd ℂ) ((n : ℂ) ^ s) = (n : ℂ) ^ ((starRingEnd ℂ) s) := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    have h0' : ((n : ℝ) : ℂ).arg = 0 :=
      Complex.arg_ofReal_of_nonneg (by exact_mod_cast (le_of_lt hn))
    have h0 : ((n : ℂ)).arg = 0 := by
      simp
    rw [h0]
    exact Real.pi_ne_zero.symm
  symm
  conv_lhs => rw [← map_natCast (starRingEnd ℂ) n]
  rw [Complex.conj_cpow (n : ℂ) ((starRingEnd ℂ) s) harg]
  simp

/-- 实现 5: 函数方程连接发散区与收敛区 (mathlib riemannZeta_one_sub) —
    发散级数 (Re ≤ 1) 的值通过发散/周期对称 (s ↔ 1-s) 从收敛区获得:
    这就是解析延拓的机制, mathlib 已机器验证。 -/
theorem functional_equation_bridges {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'

end

end DivergencePeriodSymmetry

/- ================= 习题 37 新增: 黎曼方向统一观测 (0pat) ================= -/

namespace RiemannUnifiedObservation

noncomputable section

open scoped BigOperators

/-- 素数因子零点定理: 1 - p^{-s} = 0 ⟺ ∃ k : ℤ, s·ln p = k·2πi。
    每个素数因子 (1-p^{-s}) 的零点全在 Re(s) = 0 上 (纯虚轴) —
    "素数复数进制分解"的精确内容 (Complex.exp_eq_one_iff)。 -/
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

/-- 平凡零点条件: cos(πs/2) = 0 ⟺ s = 2k+1 (k ∈ ℤ)。
    函数方程的三角因子零点 = 奇整数 (Complex.cos_eq_zero_iff)。 -/
theorem trivial_zero_condition (s : ℂ) :
    Complex.cos (↑Real.pi * s / 2) = 0 ↔ ∃ k : ℤ, s = (2 * (k : ℂ) + 1) := by
  constructor
  · intro h
    rcases (Complex.cos_eq_zero_iff).1 h with ⟨k, hk⟩
    use k
    have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hmul : (↑Real.pi * s / 2) * 2 = ((2 * (k : ℂ) + 1) * ↑Real.pi / 2) * 2 := by
      exact congrArg (fun z : ℂ => z * 2) hk
    have hπs : ↑Real.pi * s = (2 * (k : ℂ) + 1) * ↑Real.pi := by
      field_simp [h2] at hmul ⊢
      exact hmul
    have hs : s = 2 * (k : ℂ) + 1 := by
      -- π·s = (2k+1)·π ⟹ s = 2k+1 (π ≠ 0)
      apply mul_left_cancel₀ hpi
      calc
        ↑Real.pi * s = (2 * (k : ℂ) + 1) * ↑Real.pi := hπs
        _ = ↑Real.pi * (2 * (k : ℂ) + 1) := by rw [mul_comm]
    exact hs
  · rintro ⟨k, rfl⟩
    rw [Complex.cos_eq_zero_iff]
    refine ⟨k, ?_⟩
    ring

/-- 临界线观测: Re s = 1/2 ⟺ 每个级数项的模 = n^{1/2}。
    临界线 = 发散因子 n^{-1/2} 的乘积结构 (由 zeta_term_norm_split 反向)。 -/
theorem critical_line_observation (s : ℂ) :
    s.re = 1 / 2 ↔ ∀ n : ℕ, 0 < n → ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (1 / 2 : ℝ) := by
  constructor
  · intro hs n hn
    rw [DivergencePeriodSymmetry.zeta_term_norm_split n s hn]
    rw [hs]
  · intro h
    have h2 := h 2 (by norm_num)
    rw [DivergencePeriodSymmetry.zeta_term_norm_split 2 s (by norm_num)] at h2
    exact (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).1 h2


/- 假实轴 = 相对于 i 的 nat 轴: 刻度 1 = i^i = e^{-π/2} (原点 i 的 i 次后继)。
   λ 演算的 i 次后继迭代 = 乘法群 ℂ* 中生成元 i 的 i 次幂 (cpow);
   不是 Church 编码的 Nat 计数迭代 (次数是 i, 不是预设自然数)。 -/

/-- 假实轴上的 1 = i^i = e^{-π/2} — 原点 i 的 i 次后继的数值。
    λ 演算的 i 次后继迭代 = 乘性群中 i 的 i 次幂 (cpow 定义)。 -/
theorem i_pow_i_eq_exp_neg_pi_div_two : Complex.I ^ Complex.I = ↑(Real.exp (-Real.pi / 2)) := by
  rw [Complex.cpow_def_of_ne_zero (by simp : Complex.I ≠ 0)]
  rw [Complex.log_I]
  have hcalc : (↑Real.pi / 2 * Complex.I) * Complex.I = ↑(-Real.pi / 2) := by
    calc
      (↑Real.pi / 2 * Complex.I) * Complex.I = ↑Real.pi / 2 * (Complex.I * Complex.I) := by ring
      _ = ↑Real.pi / 2 * (-1) := by rw [Complex.I_mul_I]
      _ = -↑Real.pi / 2 := by ring
      _ = ↑(-Real.pi / 2) := by simp [Complex.ofReal_div, Complex.ofReal_neg]
  rw [hcalc]
  exact (Complex.ofReal_exp (-Real.pi / 2)).symm

/-- 1 ≠ i: i^i 是实数 (re = e^{-π/2} ≠ 0), i 的 re = 0。 -/
theorem i_pow_i_ne_i : Complex.I ^ Complex.I ≠ Complex.I := by
  intro h
  have hre : (Complex.I ^ Complex.I).re = Complex.I.re := congrArg Complex.re h
  rw [i_pow_i_eq_exp_neg_pi_div_two, Complex.ofReal_re, Complex.I_re] at hre
  exact (Real.exp_pos (-Real.pi / 2)).ne' hre

/-- 0 < e^{-π/2} < 1 — 假实轴上的 1 落在 (0,1) 开区间内。 -/
theorem i_pow_i_pos_lt_one : 0 < Real.exp (-Real.pi / 2) ∧ Real.exp (-Real.pi / 2) < 1 := by
  constructor
  · exact Real.exp_pos (-Real.pi / 2)
  · rw [← Real.exp_zero]
    rw [Real.exp_lt_exp]
    linarith [Real.pi_pos]

/-- 假实轴刻度 n = (i^i)^n = e^{-nπ/2} — i 的迭代的幂结构
    (n 是"相对于 i 的 nat", 从 i^i 的幂中读出, 非 Church 计数输入)。 -/
theorem axis_tick_pow (n : ℕ) : (Complex.I ^ Complex.I) ^ n = ↑(Real.exp (-Real.pi / 2 * n)) := by
  rw [i_pow_i_eq_exp_neg_pi_div_two]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← Real.exp_add]
      congr 1
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- 素数是不可分解的迭代: 素数刻度 (i^i)^p 不能写成 ((i^i)^a)^b (a,b ≥ 2)。
    幂分解 (迭代的迭代) = 指数乘法 p = a·b; 素数的乘法不可分解性 =
    刻度的幂不可分解性。 -/
theorem prime_no_power_decomposition (p : ℕ) (hp : Nat.Prime p) :
    ¬ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧
      (Real.exp (-Real.pi / 2)) ^ p = ((Real.exp (-Real.pi / 2)) ^ a) ^ b := by
  rintro ⟨a, b, ha2, hb2, h⟩
  have hlp : (Real.exp (-Real.pi / 2)) ^ p = Real.exp (-Real.pi / 2 * p) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hlb : ((Real.exp (-Real.pi / 2)) ^ a) ^ b = Real.exp (-Real.pi / 2 * (a * b)) := by
    rw [← pow_mul]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num [Nat.cast_mul]
    ring
  rw [hlp, hlb] at h
  have harg : -Real.pi / 2 * ↑p = -Real.pi / 2 * ↑(a * b) := by
    have h' : -Real.pi / 2 * ↑p = -Real.pi / 2 * (↑a * ↑b) := by
      exact Real.exp_injective h
    simpa [Nat.cast_mul] using h'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have harg2 : (↑p : ℝ) = (↑(a * b) : ℝ) := by
    have hmul := congrArg (fun z : ℝ => z * (-2 / Real.pi)) harg
    field_simp [hpi] at hmul
    exact hmul
  have hp_eq : p = a * b := by
    exact_mod_cast harg2
  have hdvd : a ∣ p := ⟨b, hp_eq⟩
  have ha_ne1 : a ≠ 1 := by omega
  have ha_p : a = p := (hp.eq_one_or_self_of_dvd a hdvd).resolve_left ha_ne1
  have hpp : p * b = p := by
    rw [ha_p] at hp_eq
    exact hp_eq.symm
  have hb1 : b = 1 := Nat.mul_left_cancel (Nat.Prime.pos hp) (by simpa using hpp)
  omega

/- 观测工具完备化 (0pat, mathlib 直接引用): ξ 整函数结构 + 级数 + 函数方程。
   相位基点观测 (Hardy Z) 的框架定理 — 零成本, 全部 mathlib 现有定理。 -/

/-- ξ 对称 (Λ₀): Λ₀(1-s) = Λ₀(s) — mathlib 直接引用 (0pat 零成本). -/
theorem xi_symmetry₀ (s : ℂ) : completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub s

/-- ξ 对称 (Λ): Λ(1-s) = Λ(s) — mathlib 直接引用. -/
theorem xi_symmetry (s : ℂ) : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- ξ 整函数: Λ₀ 处处可微 (整) — mathlib 直接引用. -/
theorem xi_entire : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedZeta₀

/-- 级数表示: Re s > 1 时 ζ(s) = Σ 1/n^s — mathlib 直接引用. -/
theorem zeta_series_form {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' (n : ℕ), 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

/-- 函数方程: ζ(1-s) = 2(2π)^{-s}Γ(s)cos(πs/2)ζ(s) — mathlib 直接引用. -/
theorem zeta_functional_equation {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'

end

end RiemannUnifiedObservation
