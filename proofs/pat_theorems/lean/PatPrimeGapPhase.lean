/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Formal.Toolkit.PatParityPrime

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatPrimeGapPhase — 素数间隔的 4 次单位根投影 (正确的周期轴)

User correction round 2 (2026-08-13): "注意, 那就说明要投影到一个奇偶性
结构完全没丢失、且周期行的轴上。并且还得选对基点。"

## 轴修正之二: 模 2 折叠丢失结构, 4 次单位根投影保留结构

PatPrimeGapAxis 已证: 模 2 折叠 (奇偶性投影) 下素数间隔全坍缩到 0 槽
(prime_gap_two_slot) — 七扭八歪的素数轴在奇偶性投影下歪斜完全消失.
用户指出: 这说明模 2 轴不对 — 要找 **奇偶性结构完全没丢失、且周期行**
的轴.

**正确的轴 = 4 次单位根投影 p ↦ I^p (模 4 相位)**:

1. **奇偶性结构完全没丢失**: 奇数 p → I^p = ±I (虚轴上两点), 偶数 p
   → I^p = ±1 (实轴上两点) — 奇偶性在 4 次单位根投影下完全保留
   (奇 → 虚轴, 偶 → 实轴), 与模 2 折叠 (全坍缩) 不同. 七扭八歪的
   素数轴投影到 4 槽环: 素数全落虚轴两点 (±I), 歪斜保留 (奇偶性
   结构没丢失: 奇素数 vs 偶素数是实/虚轴的区别).
2. **间隔 2 = 半圈 (可分辨!)**: I^(p+2) = -I^p — 间隔 2 在 4 槽环
   上是半圈 (I^2 = -1 ≠ 1), 与模 2 折叠 (2 ≡ 0 mod 2, 丢失) 不同:
   间隔 2 在 4 次单位根投影下**可见** (twin_gap_half_turn).
3. **孪生对相位和 = 0 (对称对)**: I^p + I^(p+2) = 0 — 孪生对投影
   {I^p, -I^p} 关于圆心 0 对称 (和 = 0, R170 对称对的相位版) —
   孪生对 = 间隔 2 的对称对 (R172) 在相位上的对应: 互为相反数.
4. **选对基点 = 虚轴 (奇素数域)**: 素数除 2 外全奇数 → 投影全落
   虚轴 ±I (odd_pow_I_imag) — 孪生对 (p, p+2) 都在虚轴, 且互为
   相反数 → 投影 = {I, -I} (关于圆心 0 对称). 素数的基点 2 (R171
   two_shared_basepoint) 投影到 I^2 = -1 (实轴 -1) — 唯一落在实轴
   的素数 = 基点 2: 奇偶性与素数共享基点 2 的相位版.
5. **间隔 2 vs 间隔 4 可区分**: I^2 = -1 ≠ I^4 = 1 — 4 槽环上间隔
   2 (半圈) 与间隔 4 (全圈) 不同槽 — 奇偶性结构 (间隔模 4) 没丢失
   (模 2 折叠下 2 与 4 都 → 0 槽, 丢失; 4 槽环下可区分).

**结论 (轴修正之二)**: 素数间隔的观测轴 = 4 次单位根投影 (R141 单位
根 4 槽环, R047 周期轴 J⁴=1): 奇偶性结构完全保留 (奇 → 虚轴, 偶 →
实轴), 周期行 (4 槽环), 间隔 2 = 半圈可分辨, 孪生对相位和为 0 关于
圆心对称; 基点选虚轴 (奇素数域), 基点 2 投影 = -1 (唯一实轴素数).
R172/R173 的"间隔 2 = 奇偶性折叠周期"错误: 模 2 折叠丢失间隔结构;
正确的周期轴 = 4 次单位根 (模 4 相位).

Main theorems (本文件, 全部只锚本框架):

1. `odd_pow_I_imag`: 奇数 p → re (I^p) = 0 — 奇相位落虚轴 (奇偶性
   结构在 4 次单位根投影下保留: 奇 → 虚轴).
2. `even_pow_I_real`: 偶数 p → im (I^p) = 0 — 偶相位落实轴 (偶 →
   实轴; 素数基点 2 投影 I^2 = -1 ∈ 实轴).
3. `twin_gap_half_turn`: I^(p+2) = -I^p — 间隔 2 = 半圈 (4 槽环上
   可见, 与模 2 折叠丢失对比).
4. `twin_pair_phase_opposite`: I^p + I^(p+2) = 0 — 孪生对相位和 =
   0 (关于圆心对称, R170 对称对相位版).
5. `basepoint_two_phase`: I^2 = -1 — 素数基点 2 投影到实轴 -1 (R171
   two_shared_basepoint 相位版: 唯一偶素数 = 唯一实轴素数).
6. `gap_two_vs_four_distinct`: I^2 ≠ I^4 — 间隔 2 (半圈) 与间隔 4
   (全圈) 可区分 (奇偶性结构没丢失).
7. `twin_prime_phase_perspective`: 全景 — 奇偶性保留 ∧ 间隔 2 半圈
   ∧ 孪生对相位和 0 ∧ 基点 2 投影 -1.
-/

namespace ZeroRelative

namespace PatPrimeGapPhase

/-! ## 1. 奇偶性结构在 4 次单位根投影下完全保留

奇数 p → I^p = ±I (虚轴), 偶数 p → I^p = ±1 (实轴) — 奇偶性 =
实/虚轴的区别, 完全没丢失 (与模 2 折叠全坍缩对比, PatPrimeGapAxis).
-/

/-- **奇相位落虚轴**: 奇数 p ⟹ re (I^p) = 0 — 奇素数 (除 2 外)
投影全落虚轴 (I^p = ±I; 4 次单位根 = R141 单位根 4 槽环, R047
周期轴 J⁴=1) — 奇偶性结构在 4 次单位根投影下完全保留: 奇 → 虚轴
(模 2 折叠下素数全坍缩 1 槽, 间隔全坍缩 0 槽 — 丢失; 4 槽环下
奇偶 = 实/虚轴, 保留). -/
theorem odd_pow_I_imag {p : ℕ} (hp : Odd p) : Complex.re (Complex.I ^ p) = 0 := by
  rcases hp with ⟨k, rfl⟩
  rw [pow_add, pow_mul]
  have hI2 : Complex.I ^ 2 = -1 := by norm_num
  rw [hI2]
  simp

/-! ## 2. 偶相位落实轴

偶数 p → I^p = ±1 (实轴) — 素数基点 2 (R171 唯一偶素数) 投影到
实轴 -1 (basepoint_two_phase). -/

/-- **偶相位落实轴**: 偶数 p ⟹ im (I^p) = 0 — 偶数投影全落实轴
(I^p = ±1) — 奇偶性 = 实/虚轴区别: 偶 → 实轴 (奇 → 虚轴,
odd_pow_I_imag) — 素数基点 2 (R171 唯一偶素数) 投影 I^2 = -1 ∈
实轴. -/
theorem even_pow_I_real {p : ℕ} (hp : Even p) : Complex.im (Complex.I ^ p) = 0 := by
  rcases hp with ⟨k, rfl⟩
  rw [← two_mul]
  rw [pow_mul]
  have hI2 : Complex.I ^ 2 = -1 := by norm_num
  rw [hI2]
  simp

/-! ## 3. 间隔 2 = 半圈 (4 槽环上可见)

I^(p+2) = I^p · I^2 = -I^p — 间隔 2 在 4 次单位根投影下是半圈:
I^2 = -1 ≠ 1. 与模 2 折叠对比: 2 ≡ 0 (mod 2) 丢失; 4 槽环上
间隔 2 = 半圈可分辨 — 这是"奇偶性结构没丢失"的间隔侧. -/

/-- **间隔 2 = 半圈**: I^(p+2) = -I^p — 间隔 2 在 4 次单位根投影
下是半圈 (I^(p+2) = I^p · I^2, I^2 = -1) — 4 槽环上间隔 2 **可见**
(模 2 折叠下 2 ≡ 0 mod 2 全坍缩 0 槽丢失, PatPrimeGapAxis
prime_gap_two_slot; 4 槽环下间隔 2 = 半圈可分辨) — 正确的周期轴:
间隔 2 在 4 槽环上保留奇偶性结构 (半圈 ≠ 全圈). -/
theorem twin_gap_half_turn (p : ℕ) : Complex.I ^ (p + 2) = -Complex.I ^ p := by
  rw [pow_add]
  have hI2 : Complex.I ^ 2 = -1 := by norm_num
  rw [hI2]
  ring

/-! ## 4. 孪生对相位和 = 0 (对称对, 关于圆心)

I^p + I^(p+2) = I^p - I^p = 0 — 孪生对投影 {I^p, -I^p} 关于圆心
0 对称 (和 = 0) — R170 对称对 (p+q = 2n ⟺ q-n = -(p-n)) 的相位版:
孪生对 = 相位上互为相反数的对称对. -/

/-- **孪生对相位和 = 0**: I^p + I^(p+2) = 0 — 孪生对投影 {I^p,
-I^p} 关于圆心 0 对称 (互为相反数, 和 = 0) — R170 哥德巴赫对称对
(和 = 2(p+1)) 的 4 次单位根相位版: 间隔 2 的对称对 = 相位相反数
对 — 孪生对 (p, p+2) 在 4 槽环上 = 直径两端 (半圈). -/
theorem twin_pair_phase_opposite (p : ℕ) : Complex.I ^ p + Complex.I ^ (p + 2) = 0 := by
  rw [twin_gap_half_turn p]
  ring

/-! ## 5. 选对基点: 基点 2 投影 = -1 (唯一实轴素数)

素数的基点 = 2 (R171 two_shared_basepoint: 唯一偶素数). 4 次单位根
投影下: I^2 = -1 ∈ 实轴 — 基点 2 是唯一落在实轴的素数投影; 其余
素数 (奇数) 全落虚轴 ±I. 奇偶性与素数共享基点 2 的相位版. -/

/-- **基点 2 投影 = -1**: I^2 = -1 — 素数域的基点 2 (R171
two_shared_basepoint: 唯一偶素数) 在 4 次单位根投影下落到实轴 -1
(唯一实轴素数; 奇数素数全落虚轴 ±I, odd_pow_I_imag) — 选对基点:
素数的基点 = 2, 相位 = -1 (实轴) — 奇偶性与素数共享基点 2 的
4 次单位根相位版. -/
theorem basepoint_two_phase : Complex.I ^ 2 = -1 := by
  norm_num

/-! ## 6. 间隔 2 vs 间隔 4 可区分 (奇偶性结构没丢失)

I^2 = -1, I^4 = 1 — 4 槽环上间隔 2 (半圈) 与间隔 4 (全圈) 不同槽:
奇偶性结构 (间隔模 4) 完全保留. 模 2 折叠下 2 与 4 都 → 0 槽 (丢失);
4 次单位根下可区分. -/

/-- **间隔 2 ≠ 间隔 4 (4 槽环可区分)**: I^2 ≠ I^4 — 间隔 2 (半圈)
与间隔 4 (全圈) 在 4 次单位根投影下不同槽 (I^2 = -1, I^4 = 1) —
奇偶性结构没丢失: 间隔模 4 完全保留 (模 2 折叠下 2 与 4 都 → 0 槽
丢失, PatPrimeGapAxis prime_gap_two_slot; 4 槽环下 2 ≠ 4 可区分).
-/
theorem gap_two_vs_four_distinct : Complex.I ^ 2 ≠ Complex.I ^ 4 := by
  norm_num

/-! ## 7. 偶间隔相位上界: sup ‖I^d - 1‖ = 2 (由最小间隔 d = 2 达到)

间隔 d 都是偶数 (prime_gap_even, PatPrimeGapAxis) → I^d = (-1)^(d/2)
∈ {±1} — 偶间隔投影只落实轴 {1, -1} (0 槽或 2 槽, 永不落 1/3 槽).
相位差 ‖I^d - 1‖: d ≡ 2 (mod 4) → 2 (半圈), d ≡ 0 (mod 4) → 0
(全圈) — 上确界 = 2, 由最小间隔 d = 2 达到 (半圈 = 直径 = 从 1
到 -1 的距离). 间隔 2 = 达到相位差上界的最小间隔. -/

/-- **偶间隔相位差 ≤ 2**: 偶数 d ⟹ ‖I^d - 1‖ ≤ 2 — 偶间隔投影
I^d ∈ {±1} (I^d = (-1)^(d/2); 偶数 → 0 槽或 2 槽, 永不落 1/3 槽)
— 相位差 ‖I^d - 1‖ 的上界 = 2 (半圈; d ≡ 2 mod 4 时 = 2, d ≡ 0
mod 4 时 = 0) — 间隔 d 在 4 次单位根投影下的最长相位距离 = 2.
-/
theorem even_gap_phase_bound {d : ℕ} (hd : Even d) : ‖Complex.I ^ d - 1‖ ≤ 2 := by
  rcases hd with ⟨k, hk⟩
  rw [← two_mul] at hk
  rw [hk, pow_mul]
  have hI2 : Complex.I ^ 2 = -1 := by norm_num
  rw [hI2]
  by_cases hkEven : Even k
  · have hk1 : (-1 : ℂ) ^ k = 1 := by
      rcases hkEven with ⟨j, hj⟩
      rw [hj]
      rw [pow_add, pow_mul]
      norm_num
    rw [hk1]
    norm_num
  · have hkOdd : Odd k := Nat.not_even_iff_odd.mp hkEven
    rcases hkOdd with ⟨j, hj⟩
    have hk1 : (-1 : ℂ) ^ k = -1 := by
      rw [hj]
      rw [pow_add, pow_mul]
      norm_num
    rw [hk1]
    norm_num

/-- **最小间隔 2 达到相位差上界**: ‖I^2 - 1‖ = 2 — 间隔 d = 2 (最小
素数间隔, 孪生间隔) 在 4 次单位根投影下相位差 = 2 (半圈 = 直径 =
从 1 到 -1 的距离) — 间隔 2 = 达到相位差上界的最小间隔 (上界
‖I^d - 1‖ ≤ 2, even_gap_phase_bound). -/
theorem gap_two_achieves_bound : ‖Complex.I ^ 2 - 1‖ = 2 := by
  norm_num

/-- **间隔 4 = 相位差 0 (全圈)**: ‖I^4 - 1‖ = 0 — 间隔 4 (非孪生
间隔) 在 4 次单位根投影下相位差 = 0 (全圈, 回到 1) — 与间隔 2
(半圈, 相位差 2) 对比: 4 槽环可区分间隔 2 与 4 (gap_two_vs_four_
distinct). -/
theorem gap_four_phase_zero : ‖Complex.I ^ 4 - 1‖ = 0 := by
  norm_num

/-! ## 8. 全景 (含上界)

奇偶性结构保留 (奇 → 虚轴 re=0, 偶 → 实轴 im=0) ∧ 间隔 2 = 半圈
(I^(p+2) = -I^p) ∧ 孪生对相位和 = 0 (对称对) ∧ 基点 2 投影 = -1 ∧
偶间隔相位差上界 = 2 (由间隔 2 达到) — 4 次单位根投影 = 正确的
周期轴: 奇偶性完全保留 + 周期行 (4 槽环) + 间隔 2 可见 (半圈) +
基点选虚轴 (奇素数域) + 上界 2 由最小间隔达到. -/

/-- **★素数间隔相位全景**: ① 奇相位落虚轴 (re(I^p) = 0, 奇素数
全落虚轴) ② 偶相位落实轴 (im(I^p) = 0, 基点 2 投影 -1 是唯一实轴
素数) ③ 间隔 2 = 半圈 (I^(p+2) = -I^p, 4 槽环上可见) ④ 孪生对相位
和 = 0 (关于圆心对称, 对称对) ⑤ 偶间隔相位差上界 = 2, 由最小间隔
d = 2 达到 (‖I^2 - 1‖ = 2, 半圈 = 直径) — 4 次单位根投影 = 奇偶性
不丢失的周期轴 (R141 4 槽环/R047 周期轴): 奇 → 虚轴, 偶 → 实轴,
间隔 2 = 半圈可分辨 (模 2 折叠丢失对比, PatPrimeGapAxis); 基点选
虚轴 (奇素数域), 基点 2 投影 -1; ★最小上界 = 2, 由最小间隔 2 达到.
诚实边界: 结构观测 (投影轴选择), 非素数分布理论. -/
theorem twin_prime_phase_perspective (p : ℕ) (hp : Odd p) :
    (Complex.re (Complex.I ^ p) = 0) ∧
    (Complex.I ^ (p + 2) = -Complex.I ^ p) ∧
    (Complex.I ^ p + Complex.I ^ (p + 2) = 0) ∧
    (Complex.I ^ 2 = -1) ∧
    (‖Complex.I ^ 2 - 1‖ = 2) := by
  constructor
  · exact odd_pow_I_imag hp
  · constructor
    · exact twin_gap_half_turn p
    · constructor
      · exact twin_pair_phase_opposite p
      · constructor
        · exact basepoint_two_phase
        · exact gap_two_achieves_bound

end PatPrimeGapPhase

end ZeroRelative
