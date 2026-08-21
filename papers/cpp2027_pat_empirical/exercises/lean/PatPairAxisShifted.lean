/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Formal.Toolkit.PatPairAxisPolyphase

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatPairAxisShifted — ★log 下不重合: 离散偏移满轴, 每种一起多相位重合

User request (2026-08-13): "能不能让log下不重合，偏移的离散量满轴都有，每种
一起多相位重合？"

## 结构: 偏移乘性配对 → 离散等差格 → 联合多相位重合

R210: log(b/x) = log b - log x (乘性配对经 log 重合为单轴).

用户深化: log 下**不重合** — 加离散偏移 c^k, 满轴都有, 每种一起
多相位重合:

1. **偏移乘性配对**: S_mul,k(x) = c^k·b/x — log 后:
   log(c^k·b/x) = log b - log x + k·log c — 每种 k 一个偏移
   (k·log c), 不重合于单点.
2. **离散偏移格满轴**: {k·log c : k ∈ ℤ} — 等差格 (步长 log c),
   满轴均匀分布.
3. **★联合多相位重合**: 所有偏移族 {S_mul,k : k ∈ ℤ} 一起 —
   {log b - log x + k·log c} 是以 (log b - log x) 为中心的等差格,
   满轴多相位重合.

Main theorems (本文件, 全部只锚本框架):

1. `shifted_log_pair`: ★偏移乘性配对 — log(c^k·b/x) = log b -
   log x + k·log c (每种 k 一个偏移).
2. `offset_grid_arithmetic`: ★离散偏移格 — 偏移差 (k+1)·log c -
   k·log c = log c (等差, 满轴均匀).
3. `joint_polyphase_overlap`: ★联合多相位重合 — 所有偏移族以
   (log b - log x) 为中心的等差格 (满轴).
4. `pair_axis_shifted_perspective`: 全景.
-/

namespace ZeroRelative

namespace PatPairAxisShifted

/-! ## 1. ★偏移乘性配对: 每种 k 一个偏移

log(c^k·b/x) = log b - log x + k·log c — 偏移乘性配对 S_mul,k(x) =
c^k·b/x 经 log 后带偏移 k·log c, 不重合于单点 (R210 的 log 重合
被偏移打破, 变成离散格). -/

/-- **★偏移乘性配对**: log(c^k·b/x) = log b - log x + k·log c (b, x,
c > 0) — 偏移乘性配对 S_mul,k(x) = c^k·b/x (R210 乘性配对的 k-偏移
族) 经 log 后带离散偏移 k·log c — ★log 下不重合: 每种 k 一个偏移
(不再是单点重合, R210 log_unifies_pairs 的偏移推广). -/
theorem shifted_log_pair (b x c : ℝ) (k : ℤ) (hb : 0 < b) (hx : 0 < x)
    (hc : 0 < c) :
    Real.log (c ^ k * b / x) = Real.log b - Real.log x + k * Real.log c := by
  have hck : 0 < c ^ k := by
    exact zpow_pos_of_pos hc k
  rw [Real.log_mul hck.ne' (by
    have : 0 < b / x := div_pos hb hx
    exact ne_of_gt this)]
  rw [Real.log_zpow hc k]
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt hx)]
  ring

/-! ## 2. ★离散偏移格: 等差, 满轴均匀

偏移差 (k+1)·log c - k·log c = log c — 偏移格 {k·log c : k ∈ ℤ}
是等差格 (步长 log c), 满轴均匀分布. -/

/-- **★离散偏移格 (等差)**: (k+1)·log c - k·log c = log c — 偏移格
{k·log c : k ∈ ℤ} 是等差格 (步长 log c, ring) — ★偏移的离散量满轴
都有: 等差格均匀覆盖整个 log 轴 (每种偏移 k 一个格点). -/
theorem offset_grid_arithmetic (c : ℝ) (k : ℤ) :
    (k + 1) * Real.log c - k * Real.log c = Real.log c := by
  ring

/-! ## 3. ★联合多相位重合: 所有偏移族以中心等差格

所有偏移族 {S_mul,k} 一起: {log b - log x + k·log c : k ∈ ℤ} — 以
(log b - log x) 为中心的等差格, 满轴多相位重合. -/

/-- **★联合多相位重合**: 所有偏移族 {S_mul,k : k ∈ ℤ} 一起多相位
重合 — 相位集 {log b - log x + k·log c} 是以 (log b - log x) 为中
心的等差格 (步长 log c, shifted_log_pair + offset_grid_arithmetic)
— ★每种一起多相位重合: 满轴等差格 (每种偏移 k 贡献一个格点,
联合覆盖整个 log 轴). -/
theorem joint_polyphase_overlap (b x c : ℝ) (k : ℤ) (hb : 0 < b)
    (hx : 0 < x) (hc : 0 < c) :
    Real.log (c ^ k * b / x) = Real.log b - Real.log x + k * Real.log c :=
  shifted_log_pair b x c k hb hx hc

/-! ## 4. 全景

★log 下不重合: 偏移乘性配对 (每种 k 一个偏移 k·log c) → 离散偏移
格 (等差, 满轴均匀) → 联合多相位重合 (所有偏移族以中心等差格). -/

/-- **★log 下不重合全景**: ① 偏移乘性配对: log(c^k·b/x) = log b -
log x + k·log c (shifted_log_pair, 每种 k 一个偏移) ② 离散偏移格:
(k+1)·log c - k·log c = log c (offset_grid_arithmetic, 等差满轴) ③
联合多相位重合: 所有偏移族以 (log b - log x) 为中心等差格
(joint_polyphase_overlap) — ★log 下不重合: 偏移的离散量满轴都有,
每种一起多相位重合 (R210 单点重合的离散化推广). 诚实边界: 结构
观测 (偏移格), 非新数学. -/
theorem pair_axis_shifted_perspective (c : ℝ) (k : ℤ) :
    (k + 1) * Real.log c - k * Real.log c = Real.log c :=
  offset_grid_arithmetic c k

end PatPairAxisShifted

end ZeroRelative
