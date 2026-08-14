/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Formal.Toolkit.ConciseMagicTeaching
import Formal.Toolkit.PatCountableInfinitPhaseUnification
import Formal.Toolkit.PatNondeterminism

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatPvsNPExercise — 筑基篇课后习题: P vs NP 在 pat 视角下的详细展开

Exercise (2026-08-13, 筑基篇课后习题 I): 用筑基篇定理将 R152/R153 的
P vs NP 侧写展开为详细论述. 本题只有一个论点, 不枚举:

**NP 的 pat 语义 = 用模糊换速度, 用结构找回精确.**

- **模糊** = N 的存在性: witness 的猜测不穷举 — 未锁定相位的存在性由
  相位锁定外推给出 (R150 王氏定理, R153 ③: 任意未锁定相位 θ 被 pat
  格点任意精度统一) — 这是"用模糊换速度": 不搜遍候选, 先有存在性.
- **结构** = 验证表: 有限域函数 = 预计算表 (RulerLookup, R057 一切皆表),
  表 = 结构. witness 存在 ⟺ 表条目存在, 双向 (RulerRevLookup: 表即验证) —
  这是"用结构找回精确": 模糊的猜测经表判等还原为精确的答案.
- **有限域上 P = NP 平凡** (R152): 结构已完备 (表全量), 模糊不必要 —
  求解与验证都 O(1), 多项式与常数无别.

定理只锚本框架 (R150/R152/R153/RulerLookup/RulerRevLookup), 不用外部
引理 (R153 用户纠正精神). 诚实边界: 结构侧写, 非 P≠NP 判定.

Main theorems:

1. `lookup_iff_value`: y = f x ⟺ 表条目 — 验证 = 查表判等 (结构找回精确).
2. `witness_iff_table_entry`: witness 存在 ⟺ 表条目存在 (双向) — 模糊与
   结构等价 (强化 R153 单向为双向).
3. `np_fuzzy_structure_duality`: ★NP 的模糊/结构对偶 — 模糊存在性 (∃
   witness) ∧ 结构判等 (∀ w, V x w = true ⟺ 表条目).
4. `p_np_pat_perspective`: ★全景 — N = 相位锁定外推 (模糊, R150) ∧
   验证 = 查表判等 (结构, RulerLookup/RulerRevLookup) ∧ P = 锁定方向
   唯一链 (R153 ①, R050 机制).
-/

namespace ZeroRelative

namespace PatPvsNPExercise

open MagicTeaching

/-! ## 1. 结构找回精确: 验证 = 查表判等

RulerLookup function_is_table: 有限域函数 = 预计算表; RulerRevLookup:
表即验证. 验证不重算, 只判等: y = f x ⟺ (x, y) ∈ makeTable f (双向). -/

/-- **验证 = 查表判等 (双向)**: y = f x ⟺ (x, y) ∈ makeTable f —
验证不重算, 只查表判等 (RulerLookup function_is_table: 有限域函数 = 表;
lookup_correct: 表值 = 函数值; lookup_exists: 表全量; RulerRevLookup: 表即
验证, 后向免费) — 结构找回精确: 表是结构, 判等是精确. -/
theorem lookup_iff_value {D E : Type} [Fintype D] [DecidableEq D] [DecidableEq E]
    (f : D → E) (x : D) (y : E) :
    y = f x ↔ (x, y) ∈ MagicTeaching.makeTable f := by
  constructor
  · intro h
    rw [h]
    exact MagicTeaching.lookup_exists f x
  · intro h
    exact MagicTeaching.lookup_correct f x y h

/-! ## 2. 模糊与结构等价: witness ⟺ 表条目 (双向)

R153 np_witness_in_table 是单向 (witness ⟹ 表条目); 本题强化为双向:
表条目 (w, true) ⟹ V x w = true (lookup_correct 反向) — 模糊的 witness
猜测与结构的表条目完全等价. -/

/-- **witness ⟺ 表条目 (双向)**: ∃ w, V x w = true ⟺ ∃ w, (w, true) ∈
makeTable (fun w => V x w) — 模糊的 witness 猜测与结构的表条目完全等价
(R153: 单向 witness ⟹ 表条目; RulerLookup lookup_correct: 表值 = 函数值,
表条目 ⟹ V x w = true; 本题强化为双向) — 用结构找回精确: 模糊存在性 =
结构存在性. -/
theorem witness_iff_table_entry {D : Type} [Fintype D] [DecidableEq D]
    (V : D → D → Bool) (x : D) :
    (∃ w : D, V x w = true) ↔
    (∃ w : D, (w, true) ∈ MagicTeaching.makeTable (fun w => V x w)) := by
  constructor
  · intro hw
    rcases hw with ⟨w, h⟩
    refine ⟨w, ?_⟩
    simpa [h] using MagicTeaching.lookup_exists (fun w => V x w) w
  · intro hw
    rcases hw with ⟨w, h⟩
    refine ⟨w, ?_⟩
    simpa using (MagicTeaching.lookup_correct (fun w => V x w) w true h).symm

/-! ## 3. ★NP 的模糊/结构对偶

NP 的 pat 语义 = 模糊 (存在性, 不穷举) + 结构 (判等, 精确) 同时成立:
模糊存在性 (∃ w, V x w = true) ⟹ 结构存在性 ∧ 逐点判等 — 用模糊换
速度 (先有存在性), 用结构找回精确 (表判等还原答案). -/

/-- **★NP 的模糊/结构对偶**: 存在 witness (模糊) ⟹ 表条目存在 (结构) ∧
∀ w, V x w = true ⟺ 表条目 (逐点判等) — 用模糊换速度 (存在性不穷举),
用结构找回精确 (表判等) (R152: 验证 = 可逆查表; RulerLookup/RulerRevLookup:
表即验证). -/
theorem np_fuzzy_structure_duality {D : Type} [Fintype D] [DecidableEq D]
    (V : D → D → Bool) (x : D) (hw : ∃ w : D, V x w = true) :
    (∃ w : D, (w, true) ∈ MagicTeaching.makeTable (fun w => V x w)) ∧
    (∀ w : D, V x w = true ↔ (w, true) ∈ MagicTeaching.makeTable (fun w => V x w)) := by
  constructor
  · exact (witness_iff_table_entry V x).mp hw
  · intro w
    simpa using lookup_iff_value (fun w => V x w) w true

/-! ## 4. 全景: 模糊 (N) + 结构 (验证) + 锁定 (P)

P vs NP 在 pat 视角 = 三个结构位: N = 相位锁定外推 (模糊, 存在性,
R150 王氏定理); 验证 = 查表判等 (结构, 精确, RulerLookup/RulerRevLookup);
P = 锁定方向唯一链 (R153 ①, R050 机制). 有限域上 P = NP 平凡 (R152:
结构已完备, 模糊不必要). -/

/-- **★P vs NP pat 全景**: N = 相位锁定外推 (任意相位 θ 被 pat 格点任意
精度统一, R150 王氏定理 — 模糊换速度, 存在性) ∧ 验证 = 查表判等
(∀ w, V x w = true ⟺ 表条目, RulerLookup/RulerRevLookup — 结构找回精确)
∧ P = 锁定方向唯一链 (R153 ①, R050 机制 — 无模糊). 诚实边界: 结构侧写,
非 P≠NP 判定. -/
theorem p_np_pat_perspective {D : Type} [Fintype D] [DecidableEq D]
    (V : D → D → Bool) (x : D) (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
    (∀ ε : ℝ, 0 < ε → ∃ y ∈ PatCountableInfinitPhaseUnification.patGrid, |θ - y| ≤ ε) ∧
    (∀ w : D, V x w = true ↔ (w, true) ∈ MagicTeaching.makeTable (fun w => V x w)) ∧
    (∀ d : ℝ, Function.Injective (fun x : ℝ => x + d)) := by
  constructor
  · exact PatCountableInfinitPhaseUnification.pat_phase_unification θ hθ₁ hθ₂
  · constructor
    · intro w
      simpa using lookup_iff_value (fun w => V x w) w true
    · intro d
      exact PatNondeterminism.deterministic_locked_chain_unique d

end PatPvsNPExercise

end ZeroRelative
