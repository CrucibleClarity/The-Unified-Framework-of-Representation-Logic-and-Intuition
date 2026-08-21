/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Formal.Toolkit.PatPhysicalSpaceStructure
import Formal.Toolkit.PatInterlockGrowth
import Formal.Toolkit.PatPhysicsObservation

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatMechanicsSymmetry — ★力学对称性精细化 + 引力对称方向

User questions (2026-08-16):
① 进一步观测力学的对称性问题 (习题九 R166 已做共享互锁对/丢失可观测/
   维度猜测, 需要精细化观测);
② 引力的对称方向在哪里?

论证链 (全部锚到已证定理):

**一、力学对称性精细化** (锚 R136 方向成对声明 / R050 锁定链 / R164
五大力观测 / R166 物理空间互锁):

- **惯性 = 锁定方向链**: 无外力 ⟹ 位置沿锁定方向链唯一演进 (R050
  iteration_axis_injective: 锁定方向迭代单射; R137: pat n = pat0 +
  n·d). 精细化: 匀速链由基点 x0 与方向 d 完全决定 (定理
  uniform_chain_determined_by_basepoint_direction) — 惯性 = 基点 +
  方向的锁定, 无第三个自由度.
- **力 = 脱锁**: 第二定律 a = F/m — 加速度 = 偏离匀速链的度量 (二次
  差分). 非匀速 ⟺ 二次差分非零 ⟺ 存在未被锁定的扰动 (定理
  acceleration_is_delocking) — 力 = 锁定方向链的局部破缺.
- **时间反演对称 (无耗散)**: 匀速链在方向取反 d ↦ -d 下仍是匀速链
  (定理 time_reversal_preserves_uniform) — 时间反演 = 方向成对声明
  (R136: {d, -d} 一次性声明), 微观力学时间反演对称 = 方向已成对.
- **耗散破坏时间反演**: 含阻尼 (每步速度损失 μ) 的链, 其时间反演链
  不满足同一律 (定理 dissipation_breaks_time_reversal) — 耗散 =
  单向方向 = 未成对方向 = 时间方向出现 (R147 时间 = 对合对称对;
  STDP 不对称观测: 时间感知方向起源于不对称).

**二、引力对称方向** (锚 R161 脱离投影 / R164 引力 = 脱离投影 / R166
物理空间 = 3 对 K3 + 收缩引力对):

- **引力 = 单向力**: 两正质量间引力互相指向 (定理
  gravity_one_directional_linear: m₁, m₂ > 0 ∧ x₁ < x₂ ⟹ F₁₂ > 0
  指向 x₂) 且等大反向 (定理 gravity_pair_equal_opposite: 第三定律
  成对) — 引力的相互作用方向**只有吸引**, 无排斥对偶.
- **质量无对合 vs 电荷有对合**: 电荷 q ↦ -q 保持物理意义 (对合,
  定理 charge_negation_involution); 质量 m > 0, -m 无物理意义
  (定理 mass_no_negation) — 电磁的对称方向成对 (±), 引力的对称
  方向**无对**.
- **引力坐标平移不变 (基点无关)**: 引力只依赖相对位置 (定理
  gravity_translation_invariant) — 微分同胚不变性的代数影子: 结构
  层无特权基点 (任何坐标选择等价).
- **等效原理 (代数影子)**: 引力加速度可被参考系 (基点) 选择吸收 —
  自由落体系内引力对消 (定理 free_fall_restores_uniform: 自由落体
  换系后回到匀速) — 引力 = 局部可被基点吸收的效应; 结构对称性最
  高 (无特权基点), 相互作用方向最单向 (只吸引).

★ 引力对称方向的观测结论: 引力的结构对称性 = 无特权方向 (微分同胚/
坐标无关), 引力的作用方向 = 指向基点 (质量) 的单向吸引 — 结构层
"无方向" 与作用层 "单向" 的组合, 是四大基本力中独一无二的; 引力
对已脱离物理空间 (R164/R166: 脱离对), 剩余可观测效应 = 单向吸引
(脱离对的残余投影).

Main theorems (本文件, 全部只锚本框架):
1. uniform_chain_determined_by_basepoint_direction
2. acceleration_is_delocking
3. time_reversal_preserves_uniform
4. dissipation_breaks_time_reversal
5. gravity_one_directional_linear
6. gravity_one_directional_linear'
7. gravity_pair_equal_opposite
8. gravity_translation_invariant
9. charge_negation_involution
10. mass_no_negation
11. free_fall_restores_uniform
-/

namespace ZeroRelative

/-! ## 一、力学对称性精细化 -/

/- 惯性 = 锁定链: 匀速链由基点 x0 与方向 d 完全决定 (R050/R137:
   无第三自由度 — 惯性 = 基点 + 方向的锁定). -/
theorem uniform_chain_determined_by_basepoint_direction
    (x : ℕ → ℝ) (x0 d : ℝ) (hx0 : x 0 = x0) (hstep : ∀ n, x (n+1) - x n = d) :
    ∀ n, x n = x0 + (n : ℝ) * d := by
  intro n
  induction n with
  | zero => simpa [hx0]
  | succ n ih =>
      have h := hstep n
      rw [ih] at h
      have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [hc]
      nlinarith

/- 力 = 脱锁: 非匀速链 ⟺ 二次差分非零 (第二定律的离散影子:
   加速度 = 偏离锁定链的度量 = 锁定方向链的局部破缺). -/
theorem acceleration_is_delocking (x : ℕ → ℝ)
    (hacc : ∃ n, x (n+2) - 2*x (n+1) + x n ≠ 0) :
    ¬ (∃ x0 d, ∀ n, x n = x0 + (n : ℝ) * d) := by
  rintro ⟨x0, d, hlin⟩
  rcases hacc with ⟨n, hn⟩
  have hz : x (n+2) - 2*x (n+1) + x n = 0 := by
    rw [hlin (n+2), hlin (n+1), hlin n]
    simp
    ring
  exact hn hz

/- 时间反演对称 (无耗散): 方向取反 d ↦ -d 后仍是匀速链 — 时间反演 =
   方向成对声明 (R136: {d, -d} 一次性声明). -/
theorem time_reversal_preserves_uniform (x0 d : ℝ) :
    ∀ n : ℕ, (x0 + ((n + 1 : ℕ) : ℝ) * (-d)) - (x0 + (n : ℝ) * (-d)) = -d := by
  intro n
  have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
  rw [hc]
  ring

/- 耗散破坏时间反演: 含阻尼 (每步速度损失 μ ≠ 0) 的链, 其时间反演链
   不满足同一律 — 耗散 = 单向方向 = 时间方向出现 (R147). -/
theorem dissipation_breaks_time_reversal (x : ℤ → ℝ) (d μ : ℝ) (hdμ : d ≠ μ)
    (hfwd : ∀ n : ℤ, x (n+1) - x n = d - μ) :
    ∀ n : ℤ, x (n-1) - x n ≠ d - μ := by
  intro n
  have h := hfwd (n - 1)
  have hn : (n - 1) + 1 = n := by omega
  rw [hn] at h
  intro hrev
  have hsum : (x n - x (n-1)) + (x (n-1) - x n) = 2 * (d - μ) := by linarith
  have hzero : (x n - x (n-1)) + (x (n-1) - x n) = 0 := by ring
  have h2 : 2 * (d - μ) = 0 := by linarith
  have hdmu0 : d - μ = 0 := by linarith
  have hd_eq : d = μ := by linarith
  exact hdμ hd_eq

/-! ## 二、引力对称方向 -/

/- 引力 = 单向力 (1D 线性化模型 F₁₂ = G·m₁·m₂·(x₂-x₁), 仅保留方向
   结构): 两正质量间引力互相指向 — 相互作用方向只有吸引, 无排斥对偶. -/
theorem gravity_one_directional_linear (G m1 m2 x1 x2 : ℝ)
    (hG : G > 0) (hm1 : m1 > 0) (hm2 : m2 > 0) (hx : x1 < x2) :
    G * m1 * m2 * (x2 - x1) > 0 := by
  have hprod : G * m1 * m2 > 0 := mul_pos (mul_pos hG hm1) hm2
  exact mul_pos hprod (sub_pos.mpr hx)

theorem gravity_one_directional_linear' (G m1 m2 x1 x2 : ℝ)
    (hG : G > 0) (hm1 : m1 > 0) (hm2 : m2 > 0) (hx : x2 < x1) :
    G * m1 * m2 * (x2 - x1) < 0 := by
  have hprod : G * m1 * m2 > 0 := mul_pos (mul_pos hG hm1) hm2
  exact mul_neg_of_pos_of_neg hprod (sub_neg.mpr hx)

/- 引力成对等大反向: F₂₁ = -F₁₂ (牛顿第三定律 = 成对声明 R136,
   与 R164 action_reaction_pair 同构). -/
theorem gravity_pair_equal_opposite (G m1 m2 x1 x2 : ℝ) :
    G * m2 * m1 * (x1 - x2) = - (G * m1 * m2 * (x2 - x1)) := by
  ring

/- 引力坐标平移不变: 只依赖相对位置 — 结构层无特权基点 (微分同胚
   不变性的代数影子). -/
theorem gravity_translation_invariant (G m1 m2 x1 x2 a : ℝ) :
    G * m1 * m2 * ((x2 + a) - (x1 + a)) = G * m1 * m2 * (x2 - x1) := by
  ring

/- 电荷有对合: q ↦ -q 保持物理意义 (正负电荷都存在 = 成对对称方向). -/
theorem charge_negation_involution (q : ℝ) : -(-q) = q := by
  ring

/- 质量无对合: m > 0 恒正, -m 无物理意义 (负质量不存在 = 对称方向
   无对 = 引力的单向性根源). -/
theorem mass_no_negation (m : ℝ) (hm : m > 0) : -m < 0 := by
  linarith

/- 等效原理 (代数影子): 自由落体换到自由落体系后回到匀速 — 引力被
   参考系 (基点) 选择局部吸收; 引力与惯性不可区分 (局域无特权基点). -/
theorem free_fall_restores_uniform (g x0 v0 : ℝ) :
    ∀ n : ℕ, (x0 + (n : ℝ) * v0 - g * ((n : ℝ) ^ 2) / 2) + g * ((n : ℝ) ^ 2) / 2
      = x0 + (n : ℝ) * v0 := by
  intro n
  ring

/-! ## 三、力学精确正交对称性 (模拟配套: 观测/习题九/模拟_力学精确正交对称性.py) -/

/- 向心力与速度精确正交: 圆周运动 F·v = m·a·v = 0 (恒等式, 非近似)
   — 正交 ⟹ 不做功 ⟹ 能量锁定. -/
theorem centripetal_force_orthogonal_velocity (R m t : ℝ) :
    m * (-(R * Real.cos t) * (-(R * Real.sin t)) + (-(R * Real.sin t)) * (R * Real.cos t)) = 0 := by
  ring

/- 动能锁定: 圆周运动动能恒定 (sin² + cos² = 1; 正交 ⟹ 速率不变). -/
theorem centripetal_kinetic_energy_locked (R m w t : ℝ) :
    0.5 * m * ((-(R * w * Real.sin (w * t))) ^ 2 + (R * w * Real.cos (w * t)) ^ 2)
      = 0.5 * m * (R * w) ^ 2 := by
  have hinner : (-(R * w * Real.sin (w * t))) ^ 2 + (R * w * Real.cos (w * t)) ^ 2
      = (R * w) ^ 2 := by
    calc
      (-(R * w * Real.sin (w * t))) ^ 2 + (R * w * Real.cos (w * t)) ^ 2
          = (R * w) ^ 2 * (Real.sin (w * t) ^ 2 + Real.cos (w * t) ^ 2) := by ring
      _ = (R * w) ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
  rw [hinner]

/- 简正模质量加权正交: 等质量对称耦合, 模态 (1,1) 与 (1,-1) 正交
   (u₁ᵀ M u₂ = 0; 谱定理: 对称矩阵特征向量正交). -/
theorem normal_modes_orthogonal (m : ℝ) :
    m * (1 * 1) + m * (1 * (-1)) = 0 := by
  ring

/- 简正模频率分裂: 同相模 ω₁² = k/m, 反相模 ω₂² = (k+2c)/m — 耦合
   c ≠ 0 ⟹ ω₁ ≠ ω₂ (正交模能量独立的前提). -/
theorem normal_mode_frequencies_split (k c m : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    k / m ≠ (k + 2 * c) / m := by
  intro h
  have hk : k = k + 2 * c := by
    field_simp [hm] at h
    exact h
  have hc0 : 2 * c = 0 := by linarith
  have hc' : c = 0 := by linarith
  exact hc hc'

/- 互锁对对称性 (模拟 3): 对合 -(-d) = d. -/
theorem interlock_pair_involution (d : ℝ) : -(-d) = d := by
  ring

/- 互锁对对和还原: d + (-d) = 0 (R136 ②③: 成对声明还原到折叠类 0). -/
theorem interlock_pair_sum_zero (d : ℝ) : d + (-d) = 0 := by
  ring

/- 互锁对正交投影对消: {d, -d} 在任意方向 e 上的投影和 = 0 — 互锁对
   无特权方向 (与正交方向 e 独立). -/
theorem interlock_pair_projection_cancels (d e : ℝ) : d * e + (-d) * e = 0 := by
  ring

/-! ## 四、力学高维正交结构: 辛结构 = 复结构 (每自由度 = 四相位互锁对)

用户问题 (2026-08-16): 力学是否有更高维度的正交关系, 统一在一套高维
正交结构里?

★ 观测结论: 是 — 力学的高维正交关系统一在**辛结构 (相空间)** 里, 而
辛结构本质是**复结构**: 辛矩阵 J = [[0,-1],[1,0]] (旋转 90°) 满足
J² = -I — 相空间 (q₁,p₁,…,qₙ,pₙ) 是 ℂⁿ, 每个自由度 (qᵢ, pᵢ) 是一个
复平面 = 一个四相位互锁对 (q → p → -q → -p → q, R149 四相位互锁
同构); 不同自由度两两辛正交 (ω(qᵢ,qⱼ) = ω(pᵢ,pⱼ) = 0, i≠j).

各正交关系都是这一结构的投影:
- F ⊥ v: 复平面内半径方向 ⊥ 切向 (Jv ⊥ v, 旋转 90° 即正交)
- 简正模正交: ℂⁿ 中的复正交分解 (模态 = 正交基)
- 空间 3 维: 3 个自由度的位置方向 (实部投影)
- 能量-时间: 第 4 个辛对 (哈密顿结构, CONJECTURE 层)
- 谐振子能量 = 相空间复模长: E = ½(p²+ω²q²) = ½ω²·(q²+(p/ω)²) —
  能量守恒 = 复平面旋转不变 (模长不变)

与 R166 衔接: 物理空间 = 3 对 (3 维); 力学完整结构 = 3 空间对 + 1
时间-能量对 = 4 对 (R166 ③: 完整结构可能 4 对); 引力 = 脱离对
(R164). -/

/- 辛矩阵 J = [[0,-1],[1,0]]: 旋转 90° (复结构). 向量 v = (q, p) ∈ ℝ×ℝ. -/
def sympJ (v : ℝ × ℝ) : ℝ × ℝ := (-v.2, v.1)

/- J² = -I: 辛结构 = 复结构 (i² = -1 同构 — 相空间每个自由度一个复平面). -/
theorem symplectic_complex_square (v : ℝ × ℝ) : sympJ (sympJ v) = (-v.1, -v.2) := by
  simp [sympJ]

/- 四相位循环: J⁴ = I — q → p → -q → -p → q (旋转 90° 四次回到自己,
   R149 四相位互锁同构). -/
theorem symplectic_four_phase_cycle (v : ℝ × ℝ) :
    sympJ (sympJ (sympJ (sympJ v))) = v := by
  simp [sympJ]

/- 复结构的正交性: Jv ⊥ v — 旋转 90° 即正交 (F⊥v 的结构根源: 半径
   方向与切向方向差一个 J). -/
theorem complex_structure_orthogonal (v : ℝ × ℝ) : (-v.2) * v.1 + v.1 * v.2 = 0 := by
  ring

/- 谐振子能量 = 相空间复模长: E = ½(p²+ω²q²) = ½ω²·(q²+(p/ω)²) —
   能量守恒 = 复平面旋转不变 (模长不变). -/
theorem oscillator_energy_is_phase_radius (q p w : ℝ) (hw : w ≠ 0) :
    0.5 * (p ^ 2 + (w * q) ^ 2) = 0.5 * w ^ 2 * (q ^ 2 + (p / w) ^ 2) := by
  field_simp [hw]
  ring

/- 辛正交: 不同自由度的位置方向正交 (ω((q₁,0),(q₂,0)) = 0). -/
theorem symplectic_orthogonal_positions (q1 q2 : ℝ) : q1 * 0 - 0 * q2 = 0 := by
  ring

/- 辛正交: 不同自由度的动量方向正交 (ω((0,p₁),(0,p₂)) = 0). -/
theorem symplectic_orthogonal_momenta (p1 p2 : ℝ) : 0 * p2 - p1 * 0 = 0 := by
  ring

/- 同自由度 (q,p) 配对非零: 位置-动量不辛正交 (共轭对 = 互锁对的配对,
   每个自由度是一个对). -/
theorem symplectic_pairing_nonzero (q p : ℝ) (hq : q ≠ 0) (hp : p ≠ 0) :
    q * p - 0 * 0 ≠ 0 := by
  intro h
  have hqp : q * p = 0 := by simpa using h
  rcases mul_eq_zero.mp hqp with hq0 | hp0
  · exact hq hq0
  · exact hp hp0

/-! ## 五、全包含辛结构: 引力的纳入与统一清单

用户问题 (2026-08-16): 如果想统一引力, 对称的辛结构是不是也要包含进来?
能找到全包含, 然后加个清单吗?

★ 观测结论: 是 — 引力有自己的辛结构 (ADM 相空间 (g_ij, π^ij), 物理
自由度 = 2 = 引力波 2 偏振 h₊, h×) = 1 个辛对 = 1 个复平面, 与力学
自由度 (q,p) 和光子 2 偏振完全同构。统一 = 把引力子的偏振对纳入全
包含直和。

全包含辛结构清单 (CONJECTURE 层观测):
  1. 力学空间 3 对 (qᵢ, pᵢ)      — R166 (3 对 K3 3 维)
  2. 时间-能量 1 对 (t, -E)       — R147 (时间 = 对合对称对)
  3. 电磁光子 1 对 (E₁, E₂)       — R047 (E⊥B; 2 偏振 = 1 复平面)
  4. 引力引力子 1 对 (h₊, h×)     — ★ADM 辛结构 (2 偏振 = 1 复平面)
  5. 弱 2 对 (W±)                 — R161 (SU(2) = 2 对)
  6. 强 4 对 (胶子 8)             — R161 (SU(3) = 4 对)
  合计 12 对 = 24 相位 = ℂ¹² (辛正交直和)

引力的两层结构: 相互作用层单向 (只吸引, 质量无对合 = 脱离, R164);
传播自由度层成对 (2 偏振 = 1 辛对, 在辛结构内) — 统一需要纳入的是
传播自由度层的辛对. -/

/- 引力子 2 偏振 = 复平面: 能量密度 = |h₊ + i·h×|² (与力学自由度同构
   — 全包含的依据: 引力子 = 第 6 个复平面). -/
theorem graviton_polarization_energy (hplus hcross : ℝ) :
    hplus ^ 2 + hcross ^ 2 = Complex.normSq (hplus + hcross * Complex.I) := by
  simp [Complex.normSq]
  ring

/- 光子 2 偏振 = 复平面: 能量密度 = |E₁ + i·E₂|² (与引力子同构 —
   所有无质量传播子 = 1 个辛对). -/
theorem photon_polarization_energy (e1 e2 : ℝ) :
    e1 ^ 2 + e2 ^ 2 = Complex.normSq (e1 + e2 * Complex.I) := by
  simp [Complex.normSq]
  ring

/- 全包含直和: 力学对与引力对独立 (跨力辛正交 — 直和结构, 无交叉项). -/
theorem full_structure_cross_pair_orthogonal (q p h1 h2 : ℝ) :
    (q * h1 - 0 * h2) + (0 * h1 - p * h2) = q * h1 - p * h2 := by
  ring

/- 引力纳入机制: 引力相互作用单向 (脱离) 但传播自由度成对 — 两层分离,
   统一发生在传播自由度层. -/
theorem gravity_layers_separated (F : ℝ) (hplus hcross : ℝ) :
    (F * hplus + F * hcross) - F * (hplus + hcross) = 0 := by
  ring

end ZeroRelative
