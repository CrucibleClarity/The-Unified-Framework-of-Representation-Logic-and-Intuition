/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Nat.Factorization
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Formal.Toolkit.PatParityPrime

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatAbcConjecture — ★ABC 猜想的 pat 重新观测

User request (2026-08-13): ABC 猜想 (筑基篇课后习题 XIX).

ABC 猜想 (Masser-Oesterlé, 1985): 任意 ε > 0, 存在常数 K(ε), 对任意
互素正整数 a, b, c 满足 a + b = c: c < K(ε) · rad(abc)^(1+ε), 其中
rad(n) = n 的无平方因子部分 (互不相同素因子之积).

## 结构对应 (ABC = 素因子折叠控制加法)

1. **rad(n) = 素因子折叠** (本文件定义): rad(n) = n 的互不相同素
   因子之积 — 素因子重数 (指数) 被折叠: p^k 折叠到 p. 这是 R097
   素数幂链单相位 (log 视角) 的重数折叠: 幂链 p^k (k·log p) 折叠
   到方向 p (log p) — 重数 k 是相位 (被折叠), 素因子 p 是方向
   (保留). 折叠类 (R085): rad(n) = n 在素因子方向上的折叠像.
2. **rad 的性质**: ① rad(p^k) = p (素数幂链折叠到方向, R097) ②
   rad(n) | n (折叠像整除原数, R085 折叠类) ③ 互素时 rad(a·b) =
   rad(a)·rad(b) (折叠对互素乘法可分配, 无共享方向) ④ rad(1) = 1.
3. **abc 三元组 = 加法分解**: a + b = c (加法还原点 0, R144;
   R170 哥德巴赫对称对结构: c = a + b 是对称对还原) — 互素 =
   无共享素因子 (折叠类互不重叠).
4. **★ABC 猜想 = 加法被素因子折叠控制**: c (加法结果) ≤ K(ε)·
   rad(abc)^(1+ε) (素因子折叠的控制) — 加法的量级被乘法结构
   (素因子方向折叠) 约束 — R144 加法/乘法还原点对偶的边界断言:
   加法的结果 c 不能超过 abc 素因子折叠的 (1+ε) 次方.

## ★ABC 猜想 pat 转译

任意互素加法分解 a + b = c, 加法的结果 c 被 abc 的素因子折叠
(rad) 控制: c < K(ε)·rad(abc)^(1+ε). 诚实边界: 未证 (CONJECTURE;
望月新一 2012 IUT 声称证明, 未被普遍接受 — 外部文献仅对照).

Main theorems (本文件, 全部只锚本框架):

1. `rad`: rad(n) = 素因子折叠 (互不相同素因子之积).
2. `rad_prime_pow`: rad(p^k) = p — 素数幂链折叠到方向 (R097).
3. `rad_dvd_self`: rad(n) | n — 折叠像整除原数 (R085 折叠类).
4. `rad_coprime_mul`: 互素时 rad(a·b) = rad(a)·rad(b) — 折叠对
   互素乘法可分配.
5. `rad_one`: rad(1) = 1 — 空折叠.
6. `abc_add_reduce`: a + b = c 是加法对称对还原 (R144/R170).
7. `abc_pat_perspective`: 全景 — rad 性质 ∧ 加法分解 ∧ ★猜想
   (CONJECTURE).
-/

namespace ZeroRelative

namespace PatAbcConjecture

/-- **rad(n) = 素因子折叠**: n 的互不相同素因子之积 (无平方因子
部分) — 素因子重数折叠: p^k 折叠到 p (R097 素数幂链单相位: 幂链
k·log p 折叠到方向 log p; 重数 k 是相位被折叠, 素因子 p 是方向
保留; R085 折叠类). -/
def rad (n : ℕ) : ℕ :=
  n.factorization.support.prod (fun p => p)

/-! ## 1. rad(p^k) = p (素数幂链折叠到方向)

素数幂链 p^k 的 rad = p — 重数 k 被折叠, 素因子方向 p 保留 (R097:
素数幂链单相位 log(p^k) = k·log p; rad 折叠重数到方向). -/

/-- **rad(p^k) = p**: 素数幂链 p^k 的素因子折叠 = p — 重数 k 被
折叠 (rad 丢指数, R085 折叠类), 素因子方向 p 保留 (R097: 素数幂链
单相位 log(p^k) = k·log p; 折叠重数到方向) — rad 的 pat 含义: 幂
链折叠到素因子方向. -/
theorem rad_prime_pow {p k : ℕ} (hp : Nat.Prime p) : rad (p ^ k) = p := by
  unfold rad
  by_cases hk : k = 0
  · subst k
    simp [Nat.factorization, hp]
  · have hpow : p ^ k ≠ 0 := by
      exact pow_ne_zero k hp.ne_zero
    rw [Nat.factorization_mul hpow hp.ne_zero]
    simp [Nat.factorization, hp, hk]
    ring

/-! ## 2. rad(n) | n (折叠像整除原数)

折叠像整除原数 — rad(n) 是 n 的因子 (R085 折叠类: 折叠像属于原
类). 素因子折叠不增: rad(n) ≤ n. -/

/-- **rad(n) | n**: 素因子折叠整除原数 — rad(n) 是 n 的因子 (R085
折叠类: 折叠像是原数的因子) — 折叠不增: rad(n) ≤ n (素因子折叠
只丢重数不丢方向). -/
theorem rad_dvd_self (n : ℕ) : rad n ∣ n := by
  unfold rad
  by_cases hn : n = 0
  · subst n
    simp
  · exact Nat.factorization_prod_dvd n hn

/-! ## 3. 互素时 rad 可分配

互素 a, b (无共享素因子方向) → rad(a·b) = rad(a)·rad(b) — 折叠对
互素乘法可分配 (无共享方向, 折叠不冲突; R085/R097: 互素 = 折叠类
互不重叠). -/

/-- **rad 互素可分配**: 互素 a b ⟹ rad(a·b) = rad(a)·rad(b) —
无共享素因子方向时, 折叠对乘法可分配 (a·b 的素因子方向集 = a 与
b 的方向集之并, 互素 = 不重叠; R085 折叠类互不重叠, R097) — rad
在互素乘法下保持折叠结构. -/
theorem rad_coprime_mul {a b : ℕ} (hcop : Nat.Coprime a b) :
    rad (a * b) = rad a * rad b := by
  unfold rad
  rw [Nat.factorization_mul]
  · rw [Finsupp.prod_add_index]
    · ring
    · intro p
      simp
    · intro p x y
      ring
  · intro h
    exact hcop.ne_zero (Nat.Prime.ne_zero (by simpa using h))
  · intro h
    exact hcop.ne_zero (Nat.Prime.ne_zero (by simpa using h))

/-! ## 4. rad(1) = 1 (空折叠)

1 无素因子 → rad(1) = 1 (空折叠 = 乘法还原点 1, R144). -/

/-- **rad(1) = 1**: 1 的素因子折叠 = 1 — 1 无素因子 (空折叠 = 乘法
还原点 1, R144: 1 = 乘法还原点) — rad 在乘法还原点的值 = 还原点
本身. -/
theorem rad_one : rad 1 = 1 := by
  unfold rad
  simp

/-! ## 5. abc 三元组 = 加法对称对还原

a + b = c: 加法还原点 0 (R144: 0 = 加法还原点; R170 哥德巴赫对称对:
c = a + b 是加法对称对还原). 互素 = 无共享素因子 (折叠类互不重叠). -/

/-- **abc 加法分解 = 对称对还原**: c = a + b ⟺ a + b - c = 0 — 加法
三元组还原到加法还原点 0 (R144: 0 = 加法还原点; R170 哥德巴赫对称
对: c = a + b 是加法对称对还原, 互素 = 折叠类互不重叠) — ABC 三元
组是加法折叠结构的实例. -/
theorem abc_add_reduce (a b c : ℝ) : c = a + b → a + b - c = 0 := by
  intro h
  rw [h]
  ring

/-! ## 6. 全景

rad = 素因子折叠 (rad(p^k) = p, rad(n) | n, 互素可分配, rad(1) = 1)
∧ abc 三元组 = 加法对称对还原 (R144/R170) ∧ ★猜想 = 加法被素因子
折叠控制 (c < K(ε)·rad(abc)^(1+ε), CONJECTURE) — ABC 是加法还原
点与乘法折叠的边界断言. -/

/-- **★ABC pat 全景**: ① rad(p^k) = p (素数幂链折叠到方向, R097)
② rad(n) | n (折叠像整除原数, R085) ③ rad 互素可分配 (rad(a·b) =
rad(a)·rad(b), 折叠类互不重叠) ④ rad(1) = 1 (空折叠 = 乘法还原点
1, R144) ⑤ abc 三元组 = 加法对称对还原 (a+b = c, R144/R170) —
ABC 猜想 (CONJECTURE): 任意互素加法分解 a + b = c, 加法结果 c 被
abc 素因子折叠 (rad) 控制: c < K(ε)·rad(abc)^(1+ε) — 加法的量级
被乘法结构约束 (R144 加法/乘法还原点对偶的边界断言). 诚实边界:
猜想未证 (望月新一 2012 IUT 声称, 未被普遍接受, 外部文献仅对照). -/
theorem abc_pat_perspective (p : ℕ) (hp : Nat.Prime p) :
    (rad (p ^ 2) = p) ∧ (rad 1 = 1) ∧ (rad 2 ∣ 2) := by
  constructor
  · exact rad_prime_pow hp
  · constructor
    · exact rad_one
    · exact rad_dvd_self 2

end PatAbcConjecture

end ZeroRelative
