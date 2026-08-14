/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false

/-!
# ZeroRelative/TrueSuccessor — 真正的后继: 最小 σ-闭集生成, 无 Nat 计数 (C009)

User directive (2026-08-13): "如何才能模拟出真正的后继?" 结论 — 后继必须
从"外部函数"变成"结构本身的一部分": 生成规则 σ 与基点 e 共同定义最小
σ-闭集 (交集), 不用 Nat, 不用迭代次数 ("第 n 步"是表示定理的结论, 不是
定义的输入).

★ 内生生成纪律 (C008/C009, AGENTS.md): 生成对象的定义不依赖 Nat —
禁用 Function.iterate / F^[n] / orbit : ℕ → H / 燃料参数 / "第 k 轮".
Nat 只允许出现在表示定理的结论 (Dedekind 表示: 生成的闭包结构与 N
唯一同构).

结构:

1. **生成规则**: σ : H → H (后继作为签名的一部分, 非外部函数).
2. **闭条件**: Closed σ e C := e ∈ C ∧ ∀ x ∈ C, σ x ∈ C.
3. **生成结构**: Chain σ e := {x | ∀ C, Closed σ e C → x ∈ C}
   — 最小 σ-闭集 (交集定义, 无 Nat, 无计数).
4. **闭包性质**: e ∈ Chain (基点在内); σ Chain ⊆ Chain (后继闭);
   Chain ⊆ 一切闭集 (最小性).
5. **表示定理** (Dedekind, KNOWN): σ 在 Chain 上单射 + e ∉ σ(Chain)
   ⟹ Chain ≃ ℕ — f : ℕ → Chain (f 0 = e, f (n+1) = σ (f n)) 是双射.
   Nat 出现在表示端 (结论), 不在生成定义端.
6. **泛性质 (真正的后继标志)**: 从 (Chain, e, σ) 到任意 (X, e', f')
   的同态最多一个 (唯一性, 经表示 + Nat 归纳) — 初始代数刻画的
   结构性标志.

Main theorems:

1. `chain_mem_base`: e ∈ Chain σ e (基点被生成).
2. `chain_step`: x ∈ Chain ⟹ σ x ∈ Chain (后继闭).
3. `chain_minimal`: Closed σ e C ⟹ Chain σ e ⊆ C (最小 σ-闭集).
4. `chain_is_closed`: Chain 本身闭 (e ∈ ∧ σ 闭).
5. `gen_map_mem_chain`: f n ∈ Chain (表示方向的生成元枚举).
6. `gen_map_bijective`: σ 单射 ∧ e ∉ range σ ⟹ Function.Bijective (f σ e)
   — Chain ≃ ℕ (Dedekind 表示定理).
7. `hom_unique`: 满足同态条件的映射最多一个 (泛性质, 初始性).
-/

namespace ZeroRelative

namespace TrueSuccessor

variable {H X : Type*}

/-! ## 生成结构与闭包性质

后继 = 生成规则 σ (签名的一部分), 与基点 e 一起定义最小 σ-闭集.
交集定义: x 属于 Chain 当且仅当 x 属于每个含 e 且 σ 闭的子集. -/

/-- 闭条件: C 含基点 e 且对 σ 闭. -/
def Closed (σ : H → H) (e : H) (C : Set H) : Prop :=
  e ∈ C ∧ ∀ x : H, x ∈ C → σ x ∈ C

/-- 生成结构: 最小 σ-闭集 (交集定义, 无 Nat, 无计数). -/
def Chain (σ : H → H) (e : H) : Set H :=
  {x : H | ∀ C : Set H, Closed σ e C → x ∈ C}

/-- **基点被生成**: e ∈ Chain σ e — 基点属于最小闭集 (每个含 e 的
闭集都含 e; 交集定义). -/
theorem chain_mem_base (σ : H → H) (e : H) : e ∈ Chain σ e := by
  intro C hC
  exact hC.1

/-- **后继闭**: x ∈ Chain ⟹ σ x ∈ Chain — 生成规则保持闭集 (每个
闭集都含 σ x, 因为都含 x 且闭). -/
theorem chain_step (σ : H → H) (e : H) {x : H} (hx : x ∈ Chain σ e) :
    σ x ∈ Chain σ e := by
  intro C hC
  exact hC.2 x (hx C hC)

/-- **最小性**: 任何闭集包含 Chain — 交集 ⊆ 每个成员 (最小 σ-闭集
的极小性). -/
theorem chain_minimal (σ : H → H) (e : H) {C : Set H} (hC : Closed σ e C) :
    Chain σ e ⊆ C := by
  intro x hx
  exact hx C hC

/-- **Chain 本身是闭集**: e ∈ Chain ∧ σ Chain ⊆ Chain — 交集是闭的
(基点闭 + 后继闭, 前两定理的组合). -/
theorem chain_is_closed (σ : H → H) (e : H) : Closed σ e (Chain σ e) :=
  ⟨chain_mem_base σ e, fun x hx => chain_step σ e hx⟩

/-! ## 表示定理 (Dedekind, KNOWN)

生成映射 f : ℕ → Chain (f 0 = e, f (n+1) = σ (f n)) — Nat 出现在表示
端 (结论), 不在生成定义端. 若 σ 单射且 e 不在 σ 的像中, 则 f 是
双射: Chain ≃ ℕ. -/

/-- 生成映射: f 0 = e, f (n+1) = σ (f n) — 表示方向的生成元枚举. -/
def genMap (σ : H → H) (e : H) : ℕ → H
  | 0 => e
  | n + 1 => σ (genMap σ e n)

/-- 生成映射的步进: f (n+1) = σ (f n). -/
@[simp] lemma genMap_succ (σ : H → H) (e : H) (n : ℕ) :
    genMap σ e (n + 1) = σ (genMap σ e n) := rfl

/-- **生成映射落在 Chain 中**: f n ∈ Chain σ e (∀ n) — 表示方向的
生成元枚举 (归纳: f 0 = e ∈ Chain; f (n+1) = σ(f n) ∈ Chain 由闭性).
Nat 归纳出现在表示端, 合法. -/
theorem gen_map_mem_chain (σ : H → H) (e : H) (n : ℕ) :
    genMap σ e n ∈ Chain σ e := by
  induction n with
  | zero => exact chain_mem_base σ e
  | succ n ih => exact chain_step σ e ih

/-- **生成映射单射**: σ 单射 ∧ e ∉ range σ ⟹ Injective (genMap σ e) —
不同的 n 生成不同的元素 (Nat 归纳, 表示端; 无圈: e 非像 ⟹ 不回基点;
σ 单射 ⟹ 步进不回退). -/
theorem gen_map_injective {σ : H → H} {e : H}
    (hσ : Function.Injective σ) (he : e ∉ Set.range σ) :
    Function.Injective (genMap σ e) := by
  intro a
  induction a with
  | zero =>
      intro b hab
      cases b with
      | zero => rfl
      | succ b' =>
          -- f 0 = f (b'+1) ⟹ e = σ (f b') ∈ range σ — 与 he 矛盾
          exfalso
          apply he
          have he' : e = σ (genMap σ e b') := by
            simpa [genMap] using hab
          exact ⟨genMap σ e b', he'.symm⟩
  | succ a' iha =>
      intro b hab
      cases b with
      | zero =>
          -- f (a'+1) = f 0 ⟹ σ (f a') = e — 与 he 矛盾
          exfalso
          apply he
          have he' : e = σ (genMap σ e a') := by
            simpa [genMap_succ, genMap] using hab.symm
          exact ⟨genMap σ e a', he'.symm⟩
      | succ b' =>
          -- σ (f a') = σ (f b') ⟹ f a' = f b' (σ 单射) ⟹ a' = b' (ih)
          have hab' : σ (genMap σ e a') = σ (genMap σ e b') := by
            simpa [genMap_succ] using hab
          have hσ' : genMap σ e a' = genMap σ e b' := hσ hab'
          exact congrArg Nat.succ (iha hσ')

/-- **生成映射满射 (Chain ⊆ range f)**: 像集 {f n | n ∈ ℕ} 是含 e 的
σ-闭集 ⟹ 最小性 (Chain ⊆ 像) — 不需要对 Chain 归纳, 用最小性即可. -/
theorem gen_map_surj_on_chain (σ : H → H) (e : H) :
    ∀ x : H, x ∈ Chain σ e → x ∈ Set.range (genMap σ e) := by
  intro x hx
  -- 像集是闭集: e ∈ range f (f 0 = e); σ 闭 (σ (f n) = f (n+1))
  have hclosed : Closed σ e (Set.range (genMap σ e)) := by
    constructor
    · exact ⟨0, rfl⟩
    · intro y hy
      rcases hy with ⟨n, rfl⟩
      exact ⟨n + 1, rfl⟩
  exact chain_minimal σ e hclosed hx

/-- **表示定理 (Dedekind, KNOWN)**: σ 单射 ∧ e ∉ range σ ⟹
生成映射 ℕ → Chain σ e 双射 — Chain ≃ ℕ: 生成结构与自然数唯一同构
(Dedekind 无限系统; N 是表示结论, 非生成定义参数). -/
theorem gen_map_bijective {σ : H → H} {e : H}
    (hσ : Function.Injective σ) (he : e ∉ Set.range σ) :
    Function.Bijective (fun n : ℕ => (⟨genMap σ e n, gen_map_mem_chain σ e n⟩ : Chain σ e)) := by
  constructor
  · intro a b hab
    exact gen_map_injective hσ he (congrArg Subtype.val hab)
  · intro x
    rcases gen_map_surj_on_chain σ e x.1 x.2 with ⟨n, hn⟩
    exact ⟨n, Subtype.ext hn⟩

/-! ## 泛性质: 同态唯一 (真正的后继标志)

初始代数刻画的标志: 从 (Chain, e, σ) 到任意 (X, e', f') 的同态最多
一个 — 任何满足 h e = e' ∧ h (σ x) = f' (h x) 的映射, 在 Chain 上
彼此相等 (经表示 + Nat 归纳). -/

/-- 同态条件: h 保持基点与后继 (h e = e' ∧ h (σ x) = f' (h x)). -/
def IsHom (σ : H → H) (e : H) (e' : X) (f' : X → X) (h : H → X) : Prop :=
  h e = e' ∧ ∀ x : H, h (σ x) = f' (h x)

/-- **同态唯一 (泛性质)**: 两个同态在 Chain 上相等 — 经表示
(每个生成元 = f n) + Nat 归纳 (h₁ (f n) = h₂ (f n) ∀ n) — 初始代数
(后继的结构性) 的唯一性标志. -/
theorem hom_unique {σ : H → H} {e : H} {e' : X} {f' : X → X}
    {h₁ h₂ : H → X} (hH₁ : IsHom σ e e' f' h₁) (hH₂ : IsHom σ e e' f' h₂) :
    ∀ x : H, x ∈ Chain σ e → h₁ x = h₂ x := by
  intro x hx
  -- 经表示: x = f n ⟹ 对 n 归纳 h₁ (f n) = h₂ (f n)
  rcases gen_map_surj_on_chain σ e x hx with ⟨n, rfl⟩
  have hmain : ∀ m : ℕ, h₁ (genMap σ e m) = h₂ (genMap σ e m) := by
    intro m
    induction m with
    | zero =>
        -- h₁ (f 0) = h₁ e = e' = h₂ e = h₂ (f 0)
        simp [genMap]
        exact hH₁.1.trans hH₂.1.symm
    | succ m ih =>
        -- h₁ (σ (f m)) = f' (h₁ (f m)) = f' (h₂ (f m)) = h₂ (σ (f m))
        rw [genMap_succ, hH₁.2, ih, ← hH₂.2]
  exact hmain n

end TrueSuccessor

end ZeroRelative
