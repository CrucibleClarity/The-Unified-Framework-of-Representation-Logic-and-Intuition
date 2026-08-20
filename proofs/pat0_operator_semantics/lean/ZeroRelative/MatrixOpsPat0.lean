/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# C035: 矩阵/张量的点乘叉乘 — pat0 形式化分析 (2026-08-18)

用户指令 (2026-08-18): 先把矩阵的点乘叉乘和张量的点乘叉乘用 pat0 做一次
形式化分析。

pat0 语义 (每个算符独立轴, 数值 0-1 离散, 基点簇 C028):
  - **点乘 (内积) = 轴收缩**: 两个向量沿共享轴逐分量交互后收缩为标量 —
    投影对消 (C030) 的标量化; 正交 = 点积 0 (R047 辛正交的标量形式);
    基点 = 0 (正交 = 0).
  - **叉乘 (3D) = 互锁生成第三轴**: a×b 正交于 a 与 b — 两轴互锁产生
    正交补轴 (R166 K3 完全图: 3 轴两两互锁); 自叉乘 = 0 (基点);
    基轴叉乘 êx×êy = êz (轴互锁生成第三轴).
  - **外积 (张量积) = 互锁矩阵 (R143)**: (a⊗b)[i,j] = a_i·b_j — rank-1
    矩阵 = 两轴的锁定写入 (SSM 状态更新 k⊗d 就是外积!); 行列线性:
    行 = a 的倍数, 列 = b 的倍数.
  - **矩阵乘法 = 共享轴收缩**: (AB)[i,j] = Σ_k A[i,k]·B[k,j] — 公共轴 k
    收缩 (对消), i 轴 × j 轴交互; **轴对齐是正确性核心**: 收缩要求
    "A 的列轴 = B 的行轴" — 布局转置 = 公共轴错位 = 交互完全错误.
    (这正是引擎 GGUF 布局 bug 的 pat0 解释: reshape 用 C 顺序导致
    所有权重转置, 矩阵乘法的公共轴对错, 输出与 llama 零相关.)

张量推广: 张量点乘 = 沿公共轴的收缩 (多轴对消); 张量叉乘 (张量积) =
因子轴的笛卡尔组合.
-/

namespace ZeroRelative

noncomputable section

-- ==================== 1. 点乘 (内积) = 轴收缩 ====================

-- 点乘 = 共享轴逐分量交互后收缩为标量
def dotFin {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ i, a i * b i

-- 正交 = 点积 0 (投影对消的标量化; 基点 = 0)
-- 若两个向量没有共享的非零分量 (逐轴对消), 点积 = 0
theorem dot_zero_orthogonal {n : ℕ} (a b : Fin n → ℝ)
    (h : ∀ i, a i = 0 ∨ b i = 0) : dotFin a b = 0 := by
  unfold dotFin
  apply Finset.sum_eq_zero
  intro i hi
  rcases h i with ha | hb
  · simp [ha]
  · simp [hb]

-- 单位基轴两两正交 (点积 = 0): e_i · e_j = 0 (i ≠ j)
theorem basis_dot_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    dotFin (fun k => if k = i then 1 else 0) (fun k => if k = j then 1 else 0) = 0 := by
  unfold dotFin
  -- 每项 k: (if k=i then 1 else 0) * (if k=j then 1 else 0) — k 不可能同时 = i 和 j
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : k = i
  · subst k
    simp [hij]
  · simp [hki]

-- ==================== 2. 叉乘 (ℝ³) = 互锁生成第三轴 ====================

/-- 3D 叉乘: a×b (反对称双线性), Fin 3 分量. -/
def cross3 (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then a 1 * b 2 - a 2 * b 1
    else if i = 1 then a 2 * b 0 - a 0 * b 2
    else a 0 * b 1 - a 1 * b 0

-- 自叉乘 = 0 (叉乘的基点: 轴与自身不互锁)
theorem cross_self_zero (a : Fin 3 → ℝ) : cross3 a a = 0 := by
  ext i
  fin_cases i <;> simp [cross3] <;> ring

-- 叉乘正交于两个因子 (互锁生成正交补轴, R166 K3)
theorem cross_orthogonal_left (a b : Fin 3 → ℝ) :
    a 0 * (cross3 a b) 0 + a 1 * (cross3 a b) 1 + a 2 * (cross3 a b) 2 = 0 := by
  simp [cross3]
  ring

theorem cross_orthogonal_right (a b : Fin 3 → ℝ) :
    b 0 * (cross3 a b) 0 + b 1 * (cross3 a b) 1 + b 2 * (cross3 a b) 2 = 0 := by
  simp [cross3]
  ring

-- 基轴互锁: êx × êy = êz (两轴互锁生成第三轴, K3 完全图)
theorem cross_basis :
    cross3 (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0) =
    (fun i => if i = 2 then 1 else 0) := by
  ext i
  fin_cases i <;> simp [cross3] <;> norm_num

-- 反对称: a×b = -(b×a) (互锁的取向)
theorem cross_antisymm (a b : Fin 3 → ℝ) : cross3 a b = -cross3 b a := by
  ext i
  fin_cases i <;> simp [cross3] <;> ring

-- ==================== 3. 外积 (张量积) = 互锁矩阵 (R143) ====================

/-- 外积 (rank-1 互锁矩阵): (a⊗b)[i,j] = a_i·b_j. -/
def outerFin {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => a i * b j

-- rank-1 行列式恒等式: M[i,j]·M[i',j'] = M[i,j']·M[i',j] — 行 = a 的倍数,
-- 列 = b 的倍数 (两轴完全锁定, 无独立自由度)
theorem outer_rank_one {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ)
    (i i' : Fin m) (j j' : Fin n) :
    outerFin a b i j * outerFin a b i' j' = outerFin a b i j' * outerFin a b i' j := by
  simp [outerFin]
  ring

-- ==================== 4. 矩阵乘法 = 共享轴收缩 ====================

-- 矩阵乘法: (A·B)[i,j] = Σ_k A[i,k]·B[k,j] — 公共轴 k 收缩.
-- 轴对齐: 收缩要求 A 的列轴 (k) = B 的行轴 (k); 布局转置 = 公共轴错位.
-- mathlib 现成: Matrix.mul_assoc — 收缩的轴无关性 (结合律).

-- 结合律 = 两次收缩的次序无关 (共享轴收缩的 pat0 语义)
theorem matmul_assoc_pat0 {m n p q : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin q) ℝ) :
    (A * B) * C = A * (B * C) := by
  exact Matrix.mul_assoc A B C

-- 轴对齐的类型约束: A 的列维 (n) = B 的行维 (n) — 类型系统强制公共轴一致
-- (Matrix (Fin m) (Fin n) ℝ) * (Matrix (Fin n) (Fin p) ℝ): 只有 n = n 才可乘

end

end ZeroRelative
