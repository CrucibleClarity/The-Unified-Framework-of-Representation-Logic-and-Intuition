/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# C038: 状态矩阵复结构 — 方形冗余与复数紧化 (2026-08-18)

用户发现 (2026-08-18): 内积为零 = 复制 — SSM 状态 M 的对称(发散)/反对称
(周期)各半且正交, 不是双轴独立, 而是复结构块:
  每个 2×2 块 = [a b; -b a] = aI + bJ = 复数 a+bi (J² = -I)
  - 对称部分存 a (实部), 反对称部分存 b (虚部) — 正交是 ⟨x, Jx⟩ = 0
    (J 旋转 90° 的必然性质), 不是信息独立!
  - 一个复数 2 自由度用 4 参数存 = 50% 方形冗余 ("把脑子写成方形")

R048 紧化: 发散(实部)可单射编码进周期轴(虚部) — 状态直接存复数
  [nv, dk/2, dk/2] 替代 [nv, dk, dk] 实矩阵, 压缩 50% 无损.
  前向等价: M@k = M_c @ conj(k_c) (复结构矩阵 × 实向量 = 复数乘共轭)

实测: M 复结构偏差 c=-b / a=d ≈ 3e-5 (64 层全精确); 单步 out 误差 2.4e-4.
-/

namespace ZeroRelative

noncomputable section

open Complex

-- ==================== 1. 复结构块 = 复数 ====================

-- J 矩阵 (90° 旋转, R149/C030): J² = -I
def J2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0]

-- 复结构块 [a b; -b a] = aI + bJ: 每个块由一个复数 a+bi 决定 (2 自由度)
theorem complex_block_decomp (a b : ℝ) :
    !![a, b; -b, a] = a • (1 : Matrix (Fin 2) (Fin 2) ℝ) + b • J2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [J2, Matrix.one_apply, Matrix.smul_apply]

-- J² = -I (C030 辛投影同构: 两次 90° 旋转 = 取反)
theorem j2_sq : J2 * J2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [J2, Matrix.mul_apply]

-- ==================== 2. 正交 = 复制的特征 (用户洞察) ====================

-- aI 与 bJ 正交: ⟨aI, bJ⟩ = ab·⟨I, J⟩ = 0 — 内积为零是 J 旋转的性质,
-- 不表示信息独立 (a 与 b 是同一复数 z = a+bi 的两个分量!)
theorem sym_skew_orthogonal_frobenius (a b : ℝ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ⬝ᵥ (b • J2) = 0 := by
  ext i <;> fin_cases i <;> simp [J2, Matrix.smul_apply, dotProduct] <;> norm_num

-- ==================== 3. 前向等价: M@k = M_c · conj(k_c) ====================

-- 复结构块作用于实向量 [x; y]: [a b; -b a] @ [x; y] = [ax+by; ay-bx]
-- 复数形式: (a+bi)·(x-iy) = (ax+by) + i(ay-bx) — 实部=第一分量, 虚部=第二分量
theorem complex_block_mul_equiv (a b x y : ℝ) :
    (!![a, b; -b, a] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![x, y]
      = ![((a - b * Complex.I) * (x + y * Complex.I)).re,
           ((a - b * Complex.I) * (x + y * Complex.I)).im] := by
  ext i <;> fin_cases i <;> simp [Matrix.mulVec, Matrix.vecMul, J2]
  · -- 第一分量: ax + by = Re((a-bi)(x+yi))
    rw [← ofReal_inj]
    norm_num [Complex.ext_iff]
    ring

-- ==================== 4. 自由度: 4 参数存 2 自由度 (方形冗余) ====================

-- 复结构矩阵由对角元 a 与反对角元 b 完全决定 — 每块 4 个存储位只承载
-- 2 个自由参数 (a, b) = 一个复数. 50% 冗余的严格表述:
-- 复结构块矩阵空间与 ℂ 双射 (bijective ⟹ R048 单射编码无损)
theorem complex_block_bijective (a b a' b' : ℝ) :
    (!![a, b; -b, a] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![a', b'; -b', a'] ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have h00 : a = a' := by
      have := congrFun (congrFun h 0) 0
      simpa using this
    have h01 : b = b' := by
      have := congrFun (congrFun h 0) 1
      simpa using this
    exact ⟨h00, h01⟩
  · intro h
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [h.1, h.2]

end

end ZeroRelative
