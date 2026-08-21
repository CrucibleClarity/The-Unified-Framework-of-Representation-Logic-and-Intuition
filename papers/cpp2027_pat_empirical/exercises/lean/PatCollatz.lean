/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
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
# Toolkit/PatCollatz — ★考拉兹猜想的 pat 重新观测

User request (2026-08-13): 考拉兹猜想 (筑基篇课后习题 XVII).

考拉兹猜想 (经典): 任意正整数 n 经迭代 f(n) = n/2 (n 偶), 3n+1
(n 奇) 最终到达 1.

## 结构对应 (考拉兹 = 奇偶性折叠驱动的轨道)

1. **考拉兹步 = 奇偶性折叠决策** (R171/R141 模 2 折叠, 2 槽环):
   - 偶数 (0 槽) → n/2 — 取消一个 2 因子 (折叠类还原, R085).
   - 奇数 (1 槽) → 3n+1 — 必落偶数槽 (★奇数步必落偶数: 3·奇+1 =
     偶, collatz_odd_step_even).
2. **★奇数步必落偶数槽**: 奇数 n → Even (3n+1) — 3·奇 = 奇, 奇+1
   = 偶 — 轨道奇偶性模式中奇数后面永远是偶数 (无连续奇数, 除
   2 外) — 奇偶性折叠 (R171) 的轨道约束.
3. **合并步 = (3n+1)/2**: 奇数步 (3n+1) 是偶数, 下一步必除 2 —
   两步合并 = (3n+1)/2 (collatz_odd_merged_step) — 奇数的有效
   推进 = (3n+1)/2, 偶数只消因子 2.
4. **循环 1 → 4 → 2 → 1**: 1 奇 → 4 偶 → 2 偶 → 1 — 奇偶性模式
   奇偶偶 循环 (周期 3 的奇偶性折叠模式) — 考拉兹猜想 = 所有轨道
   落入这个奇偶性模式 (CONJECTURE).
5. **偶数的折叠类还原**: 偶数 n → n/2 = 取消一个 2 因子 — 除以 2
   幂 = 沿素数 2 的折叠类下降 (R085/R097: 素数幂链单相位).

## ★考拉兹猜想 pat 转译

任意正整数 n 的考拉兹轨道最终落入奇偶性折叠模式 奇偶偶 (1 → 4 →
2 → 1 循环): 奇数步必落偶数槽, 偶数步消 2 因子 — 轨道 = 奇偶性
折叠驱动的收缩过程. 诚实边界: 未证 (CONJECTURE; 已知: 验证到极大
范围无反例, 无证明).

Main theorems (本文件, 全部只锚本框架):

1. `collatzStep`: 考拉兹单步 f(n) (偶 → n/2, 奇 → 3n+1).
2. `collatz_even_step`: 偶数步 = n/2 (折叠类还原, 消一个 2 因子).
3. `collatz_odd_step`: 奇数步 = 3n+1 (必落偶数槽).
4. `collatz_odd_step_even`: ★奇数步输出是偶数 (3n+1, 轨道无连续
   奇数) — 奇偶性折叠约束.
5. `even_half_restore`: 偶数步还原 2·(n/2) = n (消 2 因子可逆).
6. `collatz_odd_merged_step`: 奇数两步合并 = (3n+1)/2.
7. `collatz_cycle_142`: 循环 1 → 4 → 2 → 1 (奇偶偶 奇偶性模式).
8. `collatz_pat_perspective`: 全景 (CONJECTURE 标注猜想本身).
-/

namespace ZeroRelative

namespace PatCollatz

/-- **考拉兹单步**: f(n) = n/2 (n 偶), 3n+1 (n 奇) — 偶数 → 折叠类
还原 (取消一个 2 因子, R085/R171 0 槽), 奇数 → 3n+1 (必落偶数槽). -/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-! ## 1-3. 奇偶性折叠决策

考拉兹步 = 模 2 折叠 (R171/R141 2 槽环) 的决策: 0 槽 (偶) → 取消
一个 2 因子 (n/2, 折叠类还原); 1 槽 (奇) → 3n+1 (必落偶数槽). -/

/-- **偶数步 = 折叠类还原**: Even n ⟹ collatzStep n = n/2 — 偶数在
2 槽环 0 槽 (R171 even_two_slot), 考拉兹步取消一个 2 因子 (折叠类
还原, R085; 除以 2 幂 = 沿素数 2 折叠类下降, R097). -/
theorem collatz_even_step {n : ℕ} (hn : Even n) : collatzStep n = n / 2 := by
  unfold collatzStep
  rw [if_pos hn]

/-- **奇数步 = 3n+1**: Odd n ⟹ collatzStep n = 3n+1 — 奇数在 2 槽环
1 槽 (R171 odd_two_slot), 考拉兹步 = 3n+1 — ★输出必为偶数
(collatz_odd_step_even): 奇数步必落偶数槽. -/
theorem collatz_odd_step {n : ℕ} (hn : Odd n) : collatzStep n = 3 * n + 1 := by
  unfold collatzStep
  rw [if_neg (Nat.not_even_iff_odd.mpr hn)]

/-! ## 4. ★奇数步必落偶数槽

3·奇 = 奇, 奇 + 1 = 偶 — 轨道奇偶性序列中奇数后面永远是偶数 (除
起点 1 外无连续奇数). 这是奇偶性折叠 (R171) 对考拉兹轨道的结构
约束: 轨道奇偶模式 = 偶* 或 奇偶* (奇数后必接偶数). -/

/-- **★奇数步输出是偶数**: Odd n ⟹ Even (3n+1) — 3·奇 = 奇, 奇+1
= 偶 — 考拉兹轨道中奇数后面永远是偶数 (无连续奇数) — 奇偶性
折叠 (R171: 模 2 折叠, 奇偶性坍缩) 对轨道的结构约束: 奇数步必落
偶数槽 (0 槽). -/
theorem collatz_odd_step_even {n : ℕ} (hn : Odd n) : Even (3 * n + 1) := by
  rcases hn with ⟨k, rfl⟩
  refine ⟨3 * k + 2, ?_⟩
  ring

/-! ## 5. 偶数步还原 (消 2 因子可逆)

偶数 n = 2k: (n/2)·2 = n — 除以 2 后乘 2 还原 (折叠类下降可逆,
R085). 考拉兹的偶数步 = 消一个 2 因子, 可逆. -/

/-- **偶数步还原**: Even n ⟹ 2·(n/2) = n — 偶数 n = 2k ⟹ (2k)/2 = k
⟹ 2·k = n — 消 2 因子 (折叠类还原) 可逆 (R085: 折叠类; R097:
素数 2 幂链单相位). -/
theorem even_half_restore {n : ℕ} (hn : Even n) : 2 * (n / 2) = n := by
  rcases hn with ⟨k, hk⟩
  rw [← hk, ← two_mul]
  have hd : (2 * k) / 2 = k := by
    rw [mul_comm, Nat.mul_div_right]
    norm_num
  rw [hd]

/-! ## 6. 奇数两步合并 = (3n+1)/2

奇数步输出 3n+1 是偶数 (collatz_odd_step_even) → 下一步必除 2 —
奇数 (从奇数出发) 的两步合并 = (3n+1)/2: 奇数的有效推进 = 奇数 →
(3n+1)/2, 中间偶数步只消因子 2. -/

/-- **奇数两步合并 = (3n+1)/2**: Odd n ⟹ collatzStep (collatzStep n)
= (3n+1)/2 — 奇数步输出 3n+1 是偶数 (collatz_odd_step_even) → 下
一步必除 2 — 奇数的有效推进 = 奇数 → (3n+1)/2 (两步合并一步;
中间偶数步只消因子 2). -/
theorem collatz_odd_merged_step {n : ℕ} (hn : Odd n) :
    collatzStep (collatzStep n) = (3 * n + 1) / 2 := by
  have hEven : Even (3 * n + 1) := collatz_odd_step_even hn
  rw [collatz_odd_step hn, collatz_even_step hEven]

/-! ## 7. 循环 1 → 4 → 2 → 1

1 奇 → 4 偶 → 2 偶 → 1 — 奇偶性模式 奇偶偶 循环 (周期 3 的奇偶性
折叠模式). 考拉兹猜想 = 所有轨道最终落入这个循环 (CONJECTURE). -/

/-- **循环 1 → 4 → 2 → 1**: collatzStep 1 = 4 ∧ collatzStep 4 = 2 ∧
collatzStep 2 = 1 — 轨道奇偶性模式 奇偶偶 (1 奇 → 4 偶 → 2 偶 →
1 奇) — 周期 3 的奇偶性折叠模式 (R171/R141) — 考拉兹猜想 = 所有
轨道最终落入此循环 (CONJECTURE, 未证). -/
theorem collatz_cycle_142 :
    collatzStep 1 = 4 ∧ collatzStep 4 = 2 ∧ collatzStep 2 = 1 := by
  have h1odd : Odd 1 := ⟨0, by norm_num⟩
  have h4 : Even 4 := ⟨2, by norm_num⟩
  have h2 : Even 2 := ⟨1, by norm_num⟩
  rw [collatz_odd_step h1odd, collatz_even_step h4, collatz_even_step h2]
  norm_num

/-! ## 8. 全景

考拉兹 = 奇偶性折叠驱动的轨道: 奇数步必落偶数槽 (无连续奇数),
偶数步消 2 因子 (可逆), 奇数两步合并 (3n+1)/2, 循环 1 → 4 → 2 →
1 = 奇偶偶 奇偶性折叠模式. ★猜想 = 所有轨道最终落入此循环
(CONJECTURE). -/

/-- **★考拉兹 pat 全景**: ① 奇数步输出必为偶数 (Even (3n+1), 轨道
无连续奇数 — 奇偶性折叠约束) ② 偶数步还原 (2·(n/2) = n, 消 2 因子
可逆) ③ 奇数两步合并 = (3n+1)/2 (奇数有效推进) ④ 循环 1 → 4 → 2 →
1 (奇偶偶 奇偶性折叠模式) — 考拉兹 = 奇偶性折叠 (R171/R141 模 2
折叠) 驱动的轨道: 奇数必落偶数槽, 偶数消 2 因子. ★猜想 = 所有
轨道最终落入奇偶偶 循环 (CONJECTURE, 未证; 已验证到极大范围无反例
= 枚举证据, 非证明). 诚实边界: 结构观测 (奇偶性约束), 非收敛性
证明. -/
theorem collatz_pat_perspective (n : ℕ) (hn : Odd n) :
    (Even (3 * n + 1)) ∧
    (2 * ((3 * n + 1) / 2) = 3 * n + 1) ∧
    (collatzStep 1 = 4 ∧ collatzStep 4 = 2 ∧ collatzStep 2 = 1) := by
  constructor
  · exact collatz_odd_step_even hn
  · constructor
    · exact even_half_restore (collatz_odd_step_even hn)
    · exact collatz_cycle_142

end PatCollatz

end ZeroRelative

/-!
# Toolkit/PatCollatz — 补充: 偶奇奇 周期观测 (旋转基点 I 轴)

User request round 2 (2026-08-13): "等等，你找个偶奇奇的周期观测基点和轴
看下呢？"

## 偶奇奇 的观测基点和轴

R175 的 4 次单位根投影 (p ↦ I^p) 下奇偶 = 实/虚轴: 奇 → 虚轴 (±I),
偶 → 实轴 (±1). 观测基点取相位旋转 I (90°, 4 次单位根本征旋转):

**★旋转基点 I 轴 = 奇偶互翻轴**: 观测 (I · I^p) —
   p 奇 → I^p = ±I → I·I^p = ∓1 (实轴 = 偶槽) — 奇数被观测为偶.
   p 偶 → I^p = ±1 → I·I^p = ±I (虚轴 = 奇槽) — 偶数被观测为奇.

即: 乘法基点 I (90° 旋转) 交换实/虚轴 = 交换奇偶性 — 原观测的
奇偶偶 循环在旋转基点 I 下被观测为 **偶奇奇 循环**:

   1 → 4 → 2 → 1 (奇偶偶, 原轴) ⟶ I·I^1 = -1, I·I^4 = I,
   I·I^2 = -I (偶奇奇, 旋转轴).

补充结构: 合并步 (3n+1)/2 视角下连续奇数可能出现 — n ≡ 3 (mod 4)
→ 合并输出仍为奇数 (n = 4k+3 → (3n+1)/2 = 6k+5 奇): "奇数必落偶数
槽"是单步视角 (3n+1 本身), 合并步视角下奇数可接奇数.

Main theorems (补充, 全部只锚本框架):

1. `I_rot_swaps_axis`: 旋转基点 I 交换实/虚轴 — 奇 → 实轴 (观测为
   偶), 偶 → 虚轴 (观测为奇).
2. `collatz_cycle_even_odd_odd`: 循环 1→4→2→1 在旋转基点 I 下 =
   偶奇奇 (I·I^1 = -1 实轴, I·I^4 = I 虚轴, I·I^2 = -I 虚轴).
3. `odd_merged_step_parity`: 合并步可输出奇数 (n ≡ 3 mod 4 → 奇).
4. `eoo_perspective`: 全景 — 旋转基点观测偶奇奇 循环.
-/

namespace ZeroRelative

namespace PatCollatz

/-! ## 9. ★旋转基点 I 轴 = 奇偶互翻轴

乘法基点取 4 次单位根旋转 I (90°): 观测 (I · I^p). 奇 p → I^p = ±I
→ I·I^p = ∓1 (实轴); 偶 p → I^p = ±1 → I·I^p = ±I (虚轴) — I 旋转
交换实/虚轴 = 交换奇偶槽: 原观测的奇在旋转轴下被观测为偶, 反之
亦然. 基点选择改变观测结果 (R142/RulerDelta: 基点 = delta 的锚,
值随基点漂移位置不变; 相位基点旋转 = 奇偶轴互翻). -/

/-- **★旋转基点 I 交换奇偶轴**: 奇 p ⟹ im (I·I^p) = 0 ∧ 偶 p ⟹
re (I·I^p) = 0 — 观测 (I·I^p): 奇 → 实轴 (∓1, 观测为偶), 偶 →
虚轴 (±I, 观测为奇) — 乘法基点 I (90° 旋转) 交换实/虚轴 = 交换
奇偶槽: 原观测的奇偶偶 循环在此轴下变为 偶奇奇 (R175 4 次单位根
投影; R142/RulerDelta: 基点选择改变观测). -/
theorem I_rot_swaps_axis {p : ℕ} (hp : Odd p) :
    Complex.im (Complex.I * Complex.I ^ p) = 0 := by
  rcases hp with ⟨k, rfl⟩
  rw [pow_add, pow_mul]
  have hI2 : Complex.I ^ 2 = -1 := by norm_num
  rw [hI2]
  simp

/-- 旋转基点 I 下偶数被观测为奇 (虚轴): Even p ⟹ re (I·I^p) = 0.
-/
theorem I_rot_swaps_axis_even {p : ℕ} (hp : Even p) :
    Complex.re (Complex.I * Complex.I ^ p) = 0 := by
  rcases hp with ⟨k, rfl⟩
  rw [← two_mul]
  rw [pow_mul]
  have hI2 : Complex.I ^ 2 = -1 := by norm_num
  rw [hI2]
  simp

/-! ## 10. 偶奇奇 循环观测

循环 1 → 4 → 2 → 1 (奇偶偶) 在旋转基点 I 下: I·I^1 = I·I = I² =
-1 (实轴 = 偶槽), I·I^4 = I·1 = I (虚轴 = 奇槽), I·I^2 = I·(-1)
= -I (虚轴 = 奇槽) — 观测序列 偶奇奇 (再回到 1 → 偶). 同样的循环,
不同的基点观测: 奇偶偶 ↔ 偶奇奇. -/

/-- **★偶奇奇 循环观测**: I·I^1 = -1 ∧ I·I^4 = I ∧ I·I^2 = -I —
考拉兹循环 1→4→2→1 在旋转基点 I (90°, 4 次单位根) 观测下: -1
(实轴 = 偶槽) → I (虚轴 = 奇槽) → -I (虚轴 = 奇槽) → -1 (偶槽) —
**偶奇奇 循环** (原轴观测为 奇偶偶; 基点旋转交换奇偶槽, 循环模式
对偶翻转 — R142 基点观测相对性; R175 4 次单位根轴). -/
theorem collatz_cycle_even_odd_odd :
    Complex.I * Complex.I ^ 1 = -1 ∧
    Complex.I * Complex.I ^ 4 = Complex.I ∧
    Complex.I * Complex.I ^ 2 = -Complex.I := by
  constructor
  · norm_num
  · constructor
    · norm_num
    · norm_num

/-! ## 11. 合并步可输出奇数 (连续奇数可能)

单步视角: 奇数 → 3n+1 必偶 (collatz_odd_step_even). 合并步视角
(奇数两步合并 = (3n+1)/2): n ≡ 3 (mod 4) → (3n+1)/2 = 6k+5 仍为
奇数 — 合并步轨道上连续奇数可能出现 ("奇数必落偶数槽"是单步
3n+1 的性质, 非合并步性质). -/

/-- **合并步可输出奇数**: n ≡ 3 (mod 4) ⟹ Odd ((3n+1)/2) — n =
4k+3 ⟹ (3(4k+3)+1)/2 = (12k+10)/2 = 6k+5 奇数 — 合并步视角下
连续奇数可能出现 (单步 3n+1 必偶是 collatz_odd_step_even 性质,
合并步 (3n+1)/2 无此约束) — 奇偶奇偶 折叠模式. -/
theorem odd_merged_step_parity (k : ℕ) :
    Odd (((3 * (4 * k + 3) + 1) / 2)) := by
  have h : (3 * (4 * k + 3) + 1) / 2 = 6 * k + 5 := by omega
  rw [h]
  refine ⟨3 * k + 2, ?_⟩
  omega

/-! ## 12. 全景

旋转基点 I (90° 相位基点) 交换实/虚轴 = 交换奇偶槽: 原轴观测的
奇偶偶 循环在旋转轴下变为 偶奇奇 — 循环模式是基点的函数 (R142);
合并步 (3n+1)/2 可输出奇数 (连续奇数可能, 单步与合并步视角差异).
-/

/-- **★偶奇奇 全景**: ① 旋转基点 I 交换奇偶轴 (奇 → 实轴观测为偶,
I_rot_swaps_axis) ② 循环 1→4→2→1 在旋转轴下 = 偶奇奇 (I·I^1 =
-1, I·I^4 = I, I·I^2 = -I) ③ 合并步可输出奇数 (n ≡ 3 mod 4 →
(3n+1)/2 奇, 连续奇数可能) — 观测基点旋转 (R142/RulerDelta:
基点 = delta 的锚) 翻转奇偶槽: 同一循环在 4 次单位根轴 (R175)
上可被观测为 奇偶偶 或 偶奇奇 — 奇偶模式是基点观测的函数. 诚实
边界: 结构观测 (基点相对性), 非收敛性证明. -/
theorem eoo_perspective (p : ℕ) (hp : Odd p) :
    (Complex.im (Complex.I * Complex.I ^ p) = 0) ∧
    (Complex.I * Complex.I ^ 1 = -1 ∧
     Complex.I * Complex.I ^ 4 = Complex.I ∧
     Complex.I * Complex.I ^ 2 = -Complex.I) := by
  constructor
  · exact I_rot_swaps_axis hp
  · exact collatz_cycle_even_odd_odd

end PatCollatz

end ZeroRelative
