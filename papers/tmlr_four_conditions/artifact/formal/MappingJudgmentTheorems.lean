/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/MappingJudgmentTheorems — ★四定理的判定结构形式化 (符号规范/呈现合法/符号呈现/直觉精确)

用户 2026-08-16 定位: 四定理 = token 体系层间多对多映射的判定问题。

  定理一 符号规范定理: 符号 → 逻辑/直觉 多对多映射如何判定。
    判定结构: 上下文收敛 ⟹ 唯一化判定函数存在 (歧义可收敛 = 规范可判定)。
  定理二 呈现合法定理: 逻辑/直觉 → 呈现 多对多映射如何判定。
    判定结构: 等价声明 ⟹ 判定桥接 (同源多呈现); 冲突声明 ⟹ 单射可分辨
    (同呈现多源)。
  定理三 符号呈现定理: 符号 → 呈现 (P/G) 多对多映射如何判定。
    判定结构: 往返精确 (B∘A = id) ⟹ 组装单射 (符号可分辨)。
  定理四 直觉精确定理: 直觉 → 逻辑/呈现 多对多映射如何判定。
    判定结构: 两极判定 — 表示内恒真 (1 极) ∧ 跨表示恒假 (0 极) 分离。

Main theorems:

1. `context_convergence_resolvable`: 上下文收敛 ⟹ 唯一化判定存在 (定理一).
2. `equivalence_bridge_judgment`: 等价声明 ⟹ 存在性判定桥接 (定理二).
3. `conflict_declared_resolvable`: 冲突声明 (不同 ⟹ 不同) ⟹ 单射 (定理二).
4. `round_trip_precise_injective`: 往返精确 ⟹ 组装单射 (定理三).
5. `polar_judgment_separated`: 两极判定分离 — 表示内精确 ∧ 跨表示不精确
   (定理四).
-/

namespace MappingJudgment

/-! ## 定理一: 符号规范 — 上下文收敛 ⟹ 唯一化判定

符号到目标的多对多映射, 若任意上下文收敛到同一目标 (上下文无关), 则
存在唯一化判定函数 g : α → β — 映射规范可判定. -/

/-- **上下文收敛判定**: ∀ 符号 s, 所有上下文 c₁ c₂ 映射到同一目标
⟹ 存在唯一化判定函数 g (g s = f s c 对所有上下文成立). -/
theorem context_convergence_resolvable {α β γ : Type} [Nonempty γ] (f : α → γ → β) :
    (∀ s c₁ c₂, f s c₁ = f s c₂) → ∃ g : α → β, ∀ s c, g s = f s c := by
  intro h
  refine ⟨fun s => f s (Classical.choice ‹Nonempty γ›), ?_⟩
  intro s c
  exact h s (Classical.choice ‹Nonempty γ›) c

/-! ## 定理二: 呈现合法 — 等价声明桥接 + 冲突声明可分辨

同源多呈现: 等价声明 (p₁ x ↔ p₂ x) ⟹ 存在性判定桥接 (∃ p₁ ↔ ∃ p₂).
同呈现多源: 冲突声明 (a ≠ b → f a ≠ f b) ⟹ f 单射 (源可分辨). -/

/-- **等价声明桥接**: 两呈现的判定等价 ⟹ 存在性判定可桥接. -/
theorem equivalence_bridge_judgment {α : Type} (p₁ p₂ : α → Prop) :
    (∀ x, p₁ x ↔ p₂ x) → ((∃ x, p₁ x) ↔ (∃ x, p₂ x)) := by
  intro h
  constructor
  · intro ⟨x, hx⟩
    exact ⟨x, (h x).1 hx⟩
  · intro ⟨x, hx⟩
    exact ⟨x, (h x).2 hx⟩

/-- **冲突声明可分辨**: 任意不同源映射到不同呈现 ⟹ f 单射 (源唯一可辨). -/
theorem conflict_declared_resolvable {α β : Type} (f : α → β) :
    (∀ a b, a ≠ b → f a ≠ f b) → Function.Injective f := by
  intro h a b hf
  by_contra hne
  exact h a b hne hf

/-! ## 定理三: 符号呈现 — 往返精确 ⟹ 组装单射

符号-呈现往返: 解析 B 是组装 A 的左逆 (B∘A = id) ⟹ 组装单射
(不同符号呈现不同 — 符号可分辨). -/

/-- **往返精确 ⟹ 组装单射**: B (A s) = s 对所有 s ⟹ A 单射. -/
theorem round_trip_precise_injective {S P : Type} (A : S → P) (B : P → S) :
    (∀ s, B (A s) = s) → Function.Injective A := by
  intro h s₁ s₂ hA
  calc
    s₁ = B (A s₁) := (h s₁).symm
    _ = B (A s₂) := by rw [hA]
    _ = s₂ := h s₂

/-! ## 定理四: 直觉精确 — 两极判定分离

表示内精确 (所有探针判定为真, 1 极) ∧ 跨表示不精确 (所有探针判定为假,
0 极) ⟹ 两极判定成立 (判定分离: 存在精确探针 ∧ 不存在跨表示探针). -/

/-- **两极判定分离**: 表示内恒真 (h₁) ∧ 跨表示恒假 (h₂) ⟹ 存在内真探针
∧ 不存在跨表示真探针 (两极对比成立). -/
theorem polar_judgment_separated {α : Type} [Nonempty α] (in_p out_p : α → Prop)
    (h₁ : ∀ a, in_p a) (h₂ : ∀ a, ¬ out_p a) :
    (∃ a, in_p a) ∧ (¬ ∃ a, out_p a) := by
  constructor
  · exact ⟨Classical.choice ‹Nonempty α›, h₁ _⟩
  · intro ⟨a, ha⟩
    exact h₂ a ha

end MappingJudgment
