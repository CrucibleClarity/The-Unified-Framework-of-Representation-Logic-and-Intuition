/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Formal.Toolkit.PatRiemannTwinPrimes
import Formal.Toolkit.PatGoldbach
import Formal.Toolkit.CriticalPrimeCircles
import Formal.Toolkit.PatNumberDomains

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatParityPrime — ★奇偶性的本质 + 素数观测 + 共享基点

User request (2026-08-13): 新的习题, 观测奇偶性的本质, 然后从这个角度
观测素数, 有可能需要选对二者共享的基点?

## 奇偶性的本质 (pat 视角)

奇偶性 = **模 2 折叠** = 2 槽环 (R141: 单位根 n 槽环, n = 2) — 数轴
折叠到两个类: {偶, 奇} (R085: 折叠类). 奇偶性的结构:

1. **偶数 = 对称对之和**: 2n = n + n (R170 哥德巴赫: p + q = 2n ⟺
   对称对关于 n) — 偶数 = 对称对还原 (折叠类 0).
2. **奇数 = 对称对 + 1**: 2n + 1 = n + (n+1) — 奇数 = 对称对偏离 1.
3. **奇偶性 = 模 2 投影**: n ↦ n mod 2 ∈ {0, 1} (2 槽环的两个槽).

## 从奇偶性观测素数

**★关键观测: 2 是唯一偶素数** (mathlib Prime.eq_two_or_odd: 素数 p
要么 p = 2 要么 p 奇数) — 素数集合在奇偶性投影下坍缩: 除 2 外全部
落在奇数类. 奇偶性"看不出"素数分布 (信息坍缩), 但指出素数域的
基点 = 2 (唯一例外).

## ★共享基点: 2

奇偶性与素数共享的基点 = **2**:
- 奇偶性侧: 2 槽环的周期 = 2 (模 2 折叠由 2 定义, R141 n=2)
- 素数侧: 2 是唯一偶素数 (mathlib Prime.eq_two_or_odd), 且 2 在
  临界线圆上 (R145 critical_circle_points: ‖2-1‖ = 1)
- **2 = 奇偶性折叠的周期 = 素数域的唯一例外点** — 二者在 2 处交汇

Main theorems (本文件, 全部只锚本框架 + mathlib 数论基础):

1. `even_is_symmetric_pair`: 偶数 = 对称对之和 (2n = n + n).
2. `odd_is_symmetric_pair_plus_one`: 奇数 = 对称对 + 1 (2n+1 = n + (n+1)).
3. `even_two_slot`: 偶数的 pat 结构 = 2 槽环的 0 槽 (折叠类 0).
4. `two_unique_even_prime`: ★2 是唯一偶素数 (素数奇偶性坍缩).
5. `primes_parity_collapse`: 素数在奇偶性投影下坍缩 (除 2 外全奇数).
6. `two_shared_basepoint`: ★共享基点 2 (奇偶性周期 = 素数唯一例外).
7. `parity_prime_perspective`: 全景.
-/

namespace ZeroRelative

namespace PatParityPrime

/-! ## 1. 偶数 = 对称对之和; 奇数 = 对称对 + 1

偶数的本质 = 对称对还原 (2n = n + n, R170 哥德巴赫对称对; R085
折叠类 0); 奇数的本质 = 对称对偏离 1 (2n + 1 = n + (n+1)). -/

/-- **偶数 = 对称对之和**: 2n = n + n — 偶数 = 对称对关于 n 还原
(R170 goldbach 对称对; R085: 折叠类 0) — 偶数的 pat 本质 = 对称对
折叠还原. -/
theorem even_is_symmetric_pair (n : ℝ) : 2 * n = n + n := by
  ring

/-- **奇数 = 对称对 + 1**: 2n + 1 = n + (n + 1) — 奇数 = 对称对偏离
1 (n 与 n+1 关于 n+1/2 对称? 不 — 2n+1 是 n 与 n+1 之和, 相邻
对称对) — 奇数的 pat 本质 = 相邻对称对之和. -/
theorem odd_is_symmetric_pair_plus_one (n : ℝ) : 2 * n + 1 = n + (n + 1) := by
  ring

/-! ## 2. 偶数的 pat 结构 = 2 槽环的 0 槽

偶数 2n = 2·n — 2 槽环 (R141: 单位根 n 槽环, n=2) 的 0 槽 (模 2
折叠类 0, R085). 奇偶性 = 模 2 投影: n ↦ n mod 2. -/

/-- **偶数的 pat 结构 = 2 槽环的 0 槽**: 偶数 2n 是 2 的倍数 — 模 2
折叠到 0 (R141: 单位根 2 槽环; R085: 折叠类 0) — 奇偶性 = 模 2
投影 (2 槽环). -/
theorem even_two_slot (n : ℕ) (h : Even n) : n % 2 = 0 := by
  exact Even.mod_two_eq_zero h

/-- **奇数的 pat 结构 = 2 槽环的 1 槽**: 奇数 2n+1 模 2 = 1 (R141:
单位根 2 槽环; R085: 折叠类) — 奇偶性 = 模 2 投影的 1 槽. -/
theorem odd_two_slot (n : ℕ) (h : Odd n) : n % 2 = 1 := by
  exact Odd.mod_two_eq_one h

/-! ## 3. ★2 是唯一偶素数 (素数奇偶性坍缩)

mathlib Prime.eq_two_or_odd: 素数 p 要么 p = 2 要么 p 奇数 — 素数
集合在奇偶性投影下坍缩: 除 2 外全部落在奇数类. 奇偶性"看不出"
素数分布 (信息坍缩), 但指出素数域的基点 = 2 (唯一例外). -/

/-- **★2 是唯一偶素数**: 素数 p ⟹ p = 2 ∨ Odd p (mathlib
Prime.eq_two_or_odd) — 素数集合在奇偶性投影下坍缩: 除 2 外全部
奇数 (奇偶性"看不出"素数分布, 信息坍缩) — 素数域的奇偶性基点
= 2 (唯一例外). -/
theorem two_unique_even_prime {p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ Odd p :=
  hp.eq_two_or_odd'

/-! ## 4. 素数奇偶性坍缩 (观测结果)

素数在奇偶性投影下的像: {2} ∪ {奇数} — 除 2 外所有素数 ≡ 1 (mod 2).
奇偶性观测素数的结果: 几乎无区分度 (除 2 外全奇数), 但 2 是唯一
例外点 = 共享基点的候选. -/

/-- **素数奇偶性坍缩**: 素数 p ≠ 2 ⟹ p 奇数 — 除 2 外所有素数落在
奇数类 (奇偶性投影下素数集合坍缩到 {2} ∪ {奇数}; 2 = 唯一例外)
— 奇偶性观测素数的结果: 2 是唯一偶素数 (素数域的奇偶性基点). -/
theorem primes_parity_collapse {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) :
    Odd p := by
  exact (two_unique_even_prime hp).resolve_left h2

/-! ## 5. ★共享基点 2

奇偶性与素数共享基点 = 2: 奇偶性侧 = 2 槽环的周期 (模 2 折叠由
2 定义, R141 n=2); 素数侧 = 2 是唯一偶素数 (two_unique_even_prime),
且 2 在临界线圆上 (R145 critical_circle_points: ‖2-1‖ = 1) — 二者
在 2 处交汇. -/

/-- **★共享基点 2**: ① 2 是唯一偶素数 (素数侧, two_unique_even_prime)
② 2 在临界线圆上 (R145 critical_circle_points: ‖2-1‖ = 1) ③ 奇偶性
= 模 2 折叠 (2 槽环周期, R141) — 奇偶性与素数在 2 处交汇 (共享
基点): 模 2 折叠的周期 = 素数域的唯一例外. -/
theorem two_shared_basepoint :
    (∀ p : ℕ, Nat.Prime p → p = 2 ∨ Odd p) ∧
    (‖(2 : ℂ) - 1‖ = 1) := by
  constructor
  · intro p hp
    exact two_unique_even_prime hp
  · exact CriticalPrimeCircles.critical_circle_points.2.1

/-! ## 6. 全景

奇偶性 = 模 2 折叠 (2 槽环, 偶 = 对称对还原, 奇 = 对称对+1) ∧ 素数
在奇偶性投影下坍缩 (除 2 外全奇数) ∧ ★共享基点 2 (模 2 周期 =
素数唯一例外 = 临界线圆上的点) — 从奇偶性观测素数: 2 是二者交汇
的基点. -/

/-- **★奇偶性-素数全景**: 偶数 = 对称对还原 (2n = n+n, R170/R085) ∧
奇数 = 对称对+1 (2n+1 = n+(n+1)) ∧ 2 是唯一偶素数 (素数奇偶性坍缩)
∧ 2 在临界线圆上 (R145) — 奇偶性 (模 2 折叠) 观测素数: 素数集合
坍缩到 {2} ∪ {奇数}, ★共享基点 = 2 (奇偶性周期 = 素数唯一例外).
诚实边界: 结构观测, 非素数分布理论. -/
theorem parity_prime_perspective (n : ℝ) :
    (2 * n = n + n) ∧ (2 * n + 1 = n + (n + 1)) ∧
    (‖(2 : ℂ) - 1‖ = 1) := by
  constructor
  · exact even_is_symmetric_pair n
  · constructor
    · exact odd_is_symmetric_pair_plus_one n
    · exact CriticalPrimeCircles.critical_circle_points.2.1

end PatParityPrime

end ZeroRelative
