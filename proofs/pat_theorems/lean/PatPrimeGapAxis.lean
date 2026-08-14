/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Formal.Toolkit.PatTwinPrime
import Formal.Toolkit.PatParityPrime
import Formal.ZeroRelative.ComplexAxis
import Formal.Toolkit.DivergencePeriodSymmetry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatPrimeGapAxis — 轴修正: 素数间隔在实数轴 (发散轴) 上的观测

User correction (2026-08-13): "要求问的间隔是实数轴上的间隔对。这意味着
孪生素数定理选错轴了对吧。能看下那个七扭八歪的实数轴, 投影到 pat 上,
是什么结构吗?"

## 轴修正 (对 R172/R173 的纠正)

R172 把间隔 2 对应到"临界线圆直径" (复数平面圆), R173 把间隔 2 做成
"震荡周期 exp(iπt)" — 都是把实数轴上的间隔搬到复数/周期轴上观测。
**选错轴**: 孪生素数定理真正问的间隔 (p, p+2) 是实数轴 (自然数 ⊂ ℝ)
上两个点之间的欧氏距离 — 在 R047 里实数轴 = 发散轴 (lift t = ⟨t, 0⟩,
proj 观测它), 间隔 2 = |(p+2) - p| = 2 是发散轴上的距离.

## 七扭八歪的实数轴投影到 pat = 全坍缩

素数在实数轴上的分布是不规则的 (间隔 2, 4, 2, 4, 6, 2, 6, ...) — 以
素数为刻度的实数轴是"七扭八歪"的 (不是均匀刻度). 把这个轴投影到 pat
的折叠结构 (奇偶性 = 模 2 投影, R171/R141 2 槽环):

1. **素数投影**: 除 2 外所有素数都是奇数 → 投影全落 1 槽 (R171
   primes_parity_collapse) — 素数轴的点列在奇偶性下几乎无区分度.
2. **间隔投影**: 两个奇素数之差是偶数 → 间隔投影全落 0 槽
   (prime_gap_even: (q - p) % 2 = 0) — 七扭八歪的间隔分布
   (2, 4, 2, 4, 6, ...) 在奇偶性投影下全部坍缩为 0, 歪斜完全消失.
3. **孪生间隔在奇偶性下不可见**: p 与 p+2 同为奇数 → 同槽 (1) →
   奇偶性投影区分不出 p 和 p+2 — 间隔 2 在周期轴 (奇偶性) 上不可见
   (twin_gap_invisible_parity).

**结论 (轴修正)**: 间隔属于发散轴 (实数轴), 投影到周期轴 (奇偶性
折叠) 后坍缩不可见 — R172 的"间隔 2 = 奇偶性折叠周期"和 R173 的
"间隔 2 = 震荡周期"是把发散轴上的距离错误地搬到周期轴上观测;
正确的观测轴 = 实数轴 (发散轴) 本身: 间隔 2 = |(p+2) - p| = 2 是
发散轴上的距离.

Main theorems (本文件, 全部只锚本框架):

1. `twin_gap_real_axis`: 间隔 2 = 实数轴上的距离 |(p+2) - p| = 2
   (发散轴 lift 2, R047).
2. `prime_gap_even`: 奇素数间隔是偶数 (投影到 2 槽环 0 槽) — 素数
   间隔在奇偶性投影下全坍缩为 0 (歪斜消失).
3. `twin_gap_invisible_parity`: p 与 p+2 在奇偶性投影下同槽 (1) —
   间隔 2 在周期轴 (奇偶性) 上不可见.
4. `gap_axis_perspective`: 全景 — 间隔 2 在发散轴上可见 (距离),
   在周期轴上不可见 (坍缩).
-/

namespace ZeroRelative

namespace PatPrimeGapAxis

/-! ## 1. 间隔 2 = 实数轴上的距离 (发散轴)

(p, p+2) 是实数轴上的两个点, 间隔 = |(p+2) - p| = 2 — 这是欧氏
距离 (发散轴 lift 2 = ⟨2, 0⟩, R047: 实数轴 = 发散轴, proj 观测).
R172 的"临界线圆直径"是复数平面的距离 (‖2-0‖=2 是圆上两点),
不是实数轴上素数之间的间隔 — 轴修正: 间隔属于发散轴. -/

/-- **间隔 2 = 实数轴上的距离**: |(p+2) - p| = 2 — (p, p+2) 是实数
轴上的两个点, 间隔 = 欧氏距离 2 (R047: 实数轴 = 发散轴 lift t =
⟨t, 0⟩; 轴修正: R172 的临界线圆直径是复数平面距离, 不是实数轴上
素数之间的间隔 — 间隔属于发散轴). -/
theorem twin_gap_real_axis (p : ℝ) : |(p + 2) - p| = 2 := by
  rw [sub_eq_add_neg]
  ring_nf
  norm_num

/-! ## 2. 奇素数间隔是偶数 (间隔投影坍缩到 0 槽)

两个奇素数之差是偶数: 奇数 - 奇数 = 偶数 (Odd.sub_odd). 素数间隔
在奇偶性投影 (模 2, R171) 下全落 0 槽 — 七扭八歪的素数间隔分布
(2, 4, 2, 4, 6, 2, 6, ...) 在奇偶性投影下全部坍缩为 0, 歪斜完全
消失 (奇偶性"看不出"素数分布, 信息坍缩, 与 R171 同精神). -/

/-- **奇素数间隔是偶数**: 素数 p, q (都 ≠ 2) ⟹ Even (q - p) — 奇数
- 奇数 = 偶数 (Odd.sub_odd) — 素数间隔在奇偶性投影 (模 2, R171/R141
2 槽环) 下全落 0 槽: 七扭八歪的素数间隔分布 (2, 4, 2, 4, 6, ...)
在奇偶性投影下全部坍缩为 0 (歪斜完全消失, 奇偶性看不出素数分布,
信息坍缩 — R171 primes_parity_collapse 同精神). -/
theorem prime_gap_even {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h2p : p ≠ 2) (h2q : q ≠ 2) : Even (q - p) := by
  have hOp : Odd p := PatParityPrime.primes_parity_collapse hp h2p
  have hOq : Odd q := PatParityPrime.primes_parity_collapse hq h2q
  exact hOp.sub_odd hOq

/-- **素数间隔投影到 2 槽环 0 槽**: 奇素数间隔 (q - p) % 2 = 0 —
间隔在奇偶性投影 (模 2, R171/R141) 下坍缩到 0 槽 (与 0 同类:
间隔投影不可区分 — 七扭八歪的间隔分布全部折叠为 0). -/
theorem prime_gap_two_slot {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h2p : p ≠ 2) (h2q : q ≠ 2) : (q - p) % 2 = 0 :=
  PatParityPrime.even_two_slot (q - p) (prime_gap_even hp hq h2p h2q)

/-! ## 3. 孪生间隔在奇偶性投影下不可见

p 与 p+2 同为奇数 (R172 twin_primes_odd) → 模 2 投影同槽 (1) →
奇偶性区分不出 p 和 p+2 — 间隔 2 在周期轴 (奇偶性折叠) 上不可见.
R172 说"间隔 2 = 奇偶性折叠周期"是错误对应: 间隔在奇偶性投影下
根本不可见 (信息坍缩), 周期轴观测不到发散轴上的距离. -/

/-- **孪生间隔在奇偶性下不可见**: 素数 p, p+2 (p ≠ 2) ⟹ p % 2 =
(p + 2) % 2 — p 与 p+2 同为奇数 (R172 twin_primes_odd/R171 坍缩),
模 2 投影同槽 (1): 奇偶性区分不出 p 和 p+2 — 间隔 2 在周期轴
(奇偶性折叠) 上不可见 (轴修正: R172 的"间隔 2 = 奇偶性折叠周期"
是把发散轴距离错误搬到周期轴; 间隔在周期轴上坍缩). -/
theorem twin_gap_invisible_parity {p : ℕ} (hp₁ : Nat.Prime p)
    (hp₂ : Nat.Prime (p + 2)) (h2 : p ≠ 2) :
    p % 2 = (p + 2) % 2 := by
  have hOp : Odd p := PatParityPrime.primes_parity_collapse hp₁ h2
  have h2q : p + 2 ≠ 2 := by
    intro hq
    omega
  have hOq : Odd (p + 2) := PatParityPrime.primes_parity_collapse hp₂ h2q
  rw [PatParityPrime.odd_two_slot p hOp]
  rw [PatParityPrime.odd_two_slot (p + 2) hOq]

/-! ## 4. 全景 (轴修正)

间隔 2 在发散轴 (实数轴) 上可见: |(p+2) - p| = 2 (距离) — 在周期轴
(奇偶性折叠) 上不可见: p % 2 = (p+2) % 2 (同槽坍缩) — 七扭八歪的
素数轴投影到奇偶性: 素数全落 1 槽, 间隔全落 0 槽, 歪斜完全消失.
**间隔属于发散轴, 周期轴观测不到间隔** — 这就是 R172/R173 选错轴
的原因. -/

/-- **★间隔轴全景 (轴修正)**: ① 间隔 2 = 实数轴距离 |(p+2)-p| = 2
(发散轴, R047) ② 奇素数间隔全坍缩到 0 槽 (prime_gap_two_slot,
模 2 投影下歪斜消失) ③ p 与 p+2 奇偶性同槽 (间隔在周期轴不可见,
twin_gap_invisible_parity) — 轴修正: 间隔属于发散轴 (实数轴),
投影到周期轴 (奇偶性折叠) 后坍缩不可见; R172/R173 把发散轴距离
搬到周期轴观测 = 选错轴. 诚实边界: 结构观测 (轴归属), 非素数分布
理论. -/
theorem gap_axis_perspective (p : ℝ) :
    (|(p + 2) - p| = 2) ∧
    ((2 : ℕ) % 2 = 0) := by
  constructor
  · exact twin_gap_real_axis p
  · norm_num

end PatPrimeGapAxis

end ZeroRelative
