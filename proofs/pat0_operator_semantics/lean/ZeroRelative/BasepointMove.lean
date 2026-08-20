/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Basic

/-!
# C026: basepoint move of operators — 每个算符有自己的基点 (2026-08-18)

用户论点 (2026-08-18): **2×2 ≠ 实数轴上的 2 — 基点问题**。
每个算符有自己的基点:
  - 加法算符 `s(x) = x + 1` 的基点 = 0 (加法单位元; `s(0) = 1`, 迭代从 0 出发)
  - 乘法算符 `m_k(x) = k·x` 的基点 = 1 (乘法单位元; `m_k(1) = k`, 迭代从 1 出发)
  - 对称性中心不在原点: 乘法单位元 1 ≠ 加法原点 0

形式化内容 (代数恒等式在任意 ring R; 数值区分在 ℤ):
  T1 `add_iter_two`: 加法域位置 2 = s(s(0)) = 0+1+1 (从加法基点 0 出发迭代 2 次)
  T2 `mul_iter_one_eq_add_iter_two`: 乘法 1 步从基点 1: m₂(1) = 2 — 数值上恰等于
    加法 2 步 (交点: 乘法 1 步 = 加法 2 步 — 乘法基点不在加法原点, 一步乘法的
    语义在加法坐标系里膨胀为 2 步加法, 这正是"迭代了 2 次加法不是一次")
  T3 `mul_iter_two`: 乘法 2 步从基点 1: m₂(m₂(1)) = 4
  T4 `core`: 4 ≠ 2 (ℤ): 乘法 2 步 ≠ 加法 2 步 — 相同迭代次数, 不同算符
    (不同基点) → 不同位置。"2×2" 中的 2 是乘法迭代语义 (从基点 1 出发),
    不是实数轴 (加法域, 从基点 0 出发) 的 2。
  T5 `basepointMove`: T(x) = x - 1 把乘法基点 1 映到加法原点 0: T(1) = 0
  T6 `addOpInvariant`: 加法算符在基点移动下不变 (共轭):
    T(s(T⁻¹(y))) = s(y) — 平移的平移共轭仍是平移 (加法算符在基点移动下自同构)
  T7 `mulOpAffine`: 乘法算符在基点移动下变换: T(m₂(T⁻¹(y))) = 2y + 1
    — 纯乘法 → 仿射 (乘 2 再平移 1); 对称中心 (不动点) 从 0 移到 -1
  T8 `centerNotOrigin`: 共轭算符的不动点 = -1 ≠ 0 — 对称性中心不在原点

novelty: 代数内容为经典环论事实 (KNOWN); 框架语义 (每个算符自己的基点 →
迭代语义依赖基点) 为 C009 后续研究问题 (basepoint-dependent law) 的落实。
-/

namespace ZeroRelative

variable {R : Type*} [CommRing R]

/-- 加法算符 (后继): `s(x) = x + 1`. 基点 = 0 (加法单位元). -/
def addStep (x : R) : R := x + 1

/-- 乘法算符 (k 倍): `m_k(x) = k·x`. 基点 = 1 (乘法单位元). -/
def mulStep (k : R) (x : R) : R := k * x

/-- 基点移动: `T(x) = x - 1` 把乘法基点 1 映到加法原点 0. -/
def basepointMove (x : R) : R := x - 1

/-- 基点移动的逆: `T⁻¹(y) = y + 1`. -/
def basepointMoveInv (y : R) : R := y + 1

-- T1: 加法域位置 2 = s(s(0)) = 0+1+1 (从加法基点 0 出发迭代 2 次)
theorem add_iter_two {R} [CommRing R] : addStep (addStep (0 : R)) = (2 : R) := by
  norm_num [addStep]

-- T2: 乘法 1 步从基点 1: m₂(1) = 2 — 数值上恰等于加法 2 步
-- (交点: 乘法 1 步的语义在加法坐标系 = 2 步加法)
theorem mul_iter_one_eq_add_iter_two {R} [CommRing R] :
    mulStep (2 : R) (1 : R) = addStep (addStep (0 : R)) := by
  norm_num [mulStep, addStep]

-- T3: 乘法 2 步从基点 1: m₂(m₂(1)) = 4
theorem mul_iter_two {R} [CommRing R] :
    mulStep (2 : R) (mulStep (2 : R) (1 : R)) = (4 : R) := by
  norm_num [mulStep]

-- T4 (core): 乘法 2 步 ≠ 加法 2 步 (ℤ): 相同迭代次数, 不同算符 → 不同位置
theorem mul_iter_two_ne_add_iter_two : mulStep (2 : ℤ) (mulStep (2 : ℤ) (1 : ℤ)) ≠
    addStep (addStep (0 : ℤ)) := by
  unfold mulStep addStep
  decide

-- T5: 基点移动把乘法基点 1 映到加法原点 0
theorem basepointMove_center : basepointMove (1 : R) = (0 : R) := by
  simp [basepointMove]

-- 基点移动对合: T⁻¹ 是 T 的逆 (两侧)
theorem move_inv_right (y : R) : basepointMove (basepointMoveInv y) = y := by
  simp [basepointMove, basepointMoveInv, sub_eq_add_neg, add_assoc]

theorem move_inv_left (x : R) : basepointMoveInv (basepointMove x) = x := by
  simp [basepointMove, basepointMoveInv, sub_eq_add_neg, add_assoc]

-- T6: 加法算符在基点移动下不变 (共轭): T(s(T⁻¹(y))) = s(y)
-- 平移的平移共轭仍是平移 — 加法算符在基点移动下自同构
theorem addOpInvariant (y : R) :
    basepointMove (addStep (basepointMoveInv y)) = addStep y := by
  unfold basepointMove basepointMoveInv addStep
  ring

-- T7: 乘法算符在基点移动下变换: T(m₂(T⁻¹(y))) = 2y + 1
-- 纯乘法 → 仿射 (乘 2 再平移 1)
theorem mulOpAffine (y : R) :
    basepointMove (mulStep (2 : R) (basepointMoveInv y)) = (2 : R) * y + 1 := by
  unfold basepointMove basepointMoveInv mulStep
  ring

-- T8: 共轭后的乘法算符 (仿射 2y+1) 的不动点在 -1, 不在原点
-- 对称性中心不在原点 (ℤ 中; 一般 ring 需 char ≠ 2)
theorem centerIsMinusOne_int : (fun y : ℤ => 2 * y + 1) (-1 : ℤ) = (-1 : ℤ) := by
  norm_num

theorem centerNotOrigin_int : (fun y : ℤ => 2 * y + 1) (0 : ℤ) ≠ (0 : ℤ) := by
  norm_num


/-!
# C027: iteration count is basepoint-defined — 迭代次数是基点定义的 (2026-08-18)

用户批判 (2026-08-18): C026 的基点移动 T(x)=x-1 是"整体平移 1" — 反逻辑反直觉。
因为迭代本身是基点定义的: 迭代次数 n 的语义 = "从基点 e 出发迭代 n 次", 是
相对基点的位置, 不是绝对数值。基点移动后迭代语义必须变:

  - 基点 0 (加法域): 迭代算符 = 后继 +1 → n 次迭代的位置 = n (算术链)
  - 基点 1 (乘法域): 迭代算符 = 乘 m → n 次迭代的位置 = m^n (幂链)
    "乘法可能是幂运算" — 基点移到乘法单位元 1, 迭代从算术变成幂。
  - 幂链不是加法链的平移: ∄c, ∀n, m^n = n + c — 基点移动不是"整体平移 1"。
-/

-- 相对基点 e 的 n 次迭代 (表示定理: n 是"从 e 出发第 n 步", 相对位置)
def iterAt {α : Type*} (e : α) (σ : α → α) (n : ℕ) : α := σ^[n] e

-- 定理 1 (core): 同一迭代次数 n=2, 基点 0 (加法) 与基点 1 (乘法) 给出不同位置
-- 2 ≠ 4: 迭代次数是基点定义的
theorem iter_count_basepoint_dependent :
    iterAt (0 : ℕ) (fun x => x + 1) 2 ≠ iterAt (1 : ℕ) (fun x => 2 * x) 2 := by
  unfold iterAt
  decide

-- 定理 2: 乘法域的迭代 = 幂运算 (基点 1, 迭代乘 m 的 n 次 = m^n)
theorem mul_iter_is_pow (m n : ℕ) : iterAt (1 : ℕ) (fun x => m * x) n = m ^ n := by
  induction n with
  | zero => simp [iterAt]
  | succ n ih =>
      simp [iterAt, ih, Function.iterate_succ_apply', pow_succ, Nat.mul_comm]

-- 定理 3: 幂链不是加法链的平移 — 基点移动不是"整体平移 c"
theorem pow_chain_not_translation (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∃ c : ℕ, ∀ n : ℕ, m ^ n = n + c := by
  rintro ⟨c, h⟩
  have h0 := h 0
  have h2 := h 2
  norm_num at h0
  rw [← h0] at h2
  norm_num at h2
  have hm2 : 4 ≤ m ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hm hm
  have hle : (3 : ℕ) ≥ 4 := by
    rw [← h2]
    exact hm2
  omega

end ZeroRelative
