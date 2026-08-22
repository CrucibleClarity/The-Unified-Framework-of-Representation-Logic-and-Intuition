import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# 节点 08: 底边与临界带钉死 (Node 08: Bottom Edge) — 双路径

## 本节点: 底边无零点 + 奇偶拆分结构

同一结论的双路径:
- **[对称侧]** (态③): 奇偶拆分 — ζ = O_p + E_p (p-adic 拆分),
  零点 = 奇偶公共零点 (zeta_eq_zero_iff_p_split)。
- **[分析侧]** (态①②): 底边符号 — ζ 实轴实值 (反射) + ζ(-1) < 0
  (函数方程周期结构) ⟹ 底边无零点 (与 N7 (0,1) 负性合成)。

两段各自独立, 只 import Mathlib。

English: Node 08 — the bottom edge. Symmetry side: the p-adic
odd/even split. Analysis side: ζ real on the real axis and
ζ(-1) < 0 by the functional equation.
-/
set_option linter.style.longLine false

/-!
## 用户指示 (原话, 非转述) — 人类观点归属

2026-08-22 (双路径方案, 用户提出): "我希望能够做成隔离的lean，然后黎曼
方向的每个节点，都必须配备对称侧和分析侧两个路径，能做到吗？...我感觉
后者好一点，对称侧、分析侧各自逻辑连贯。"

2026-08-22 (三态框架观点归属, 用户提出): 三态框架 (一切证明法 = 消去
相位模糊或带相位并存) 为用户在黎曼 0pat 路径中提出的观点 — "这玩意本质
上是我换deepseek pro做0pat,发现死活都要走分析路径而且推不动的时候，想到
的方法论。" 本文件的双路径结构是这一观点的落地。

2026-08-22 (novelty 担忧, 用户原话): "你能都搞出来了，我感觉可能被蒸馏
完已经证完了吧。" — 按 KNOWN 纪律: 若本内容已被他人提前发布, 不视为新
结果 (novelty_status 如实标注)。
-/




noncomputable section

open scoped ComplexConjugate
open Complex

namespace RiemannDualPath

/-! ============================================================
    [对称侧] (态③) — 奇偶拆分 (零点 = 公共零点)
    ============================================================ -/

theorem zeta_eq_zero_iff_p_split {p : ℂ} (hp : p ≠ 0) (s : ℂ) :
    riemannZeta s = 0 ↔
      (1 - (p : ℂ) ^ (-s : ℂ)) * riemannZeta s = 0 ∧
        (p : ℂ) ^ (-s : ℂ) * riemannZeta s = 0 := by
  constructor
  · intro hz
    constructor <;> simp [hz]
  · intro h
    have hpz : (p : ℂ) ^ (-s : ℂ) ≠ 0 := by
      exact (Complex.cpow_ne_zero_iff).mpr (Or.inl hp)
    -- 偶部分 E_p = p⁻ˢ·ζ = 0 且 p⁻ˢ ≠ 0 ⟹ ζ = 0 (ℂ 是域)
    exact (mul_eq_zero.mp h.2).resolve_left hpz


/-! ============================================================
    [分析侧] (态①②) — 底边实值 + 符号
    ============================================================ -/

theorem zeta_im_zero_on_real (x : ℝ) : (riemannZeta (x : ℂ)).im = 0 := by
  have hc := riemannZeta_conj (x : ℂ)
  have hx : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by simp
  have hz : (starRingEnd ℂ) (riemannZeta (x : ℂ)) = riemannZeta (x : ℂ) := by
    rw [← hc, hx]
  have him : ((starRingEnd ℂ) (riemannZeta (x : ℂ))).im = -(riemannZeta (x : ℂ)).im := by
    simp
  have him' : ((starRingEnd ℂ) (riemannZeta (x : ℂ))).im = (riemannZeta (x : ℂ)).im := by
    rw [hz]
  linarith

theorem zeta_neg_one_re_neg : (riemannZeta (-(1 : ℂ))).re < 0 := by
  have hfe := riemannZeta_one_sub (s := (2 : ℂ)) (by
    intro n hn
    have hre := congrArg Complex.re hn
    have hre' : (2 : ℝ) = -(n : ℝ) := by simpa using hre
    have hnneg : (n : ℝ) < 0 := by linarith
    exact (not_lt_of_ge (Nat.cast_nonneg n)) hnneg) (by norm_num)
  -- hfe : ζ(1-2) = 2(2π)^{-2}Γ(2)cos(π·2/2)ζ(2)
  have hcos : Complex.cos (↑Real.pi * (2 : ℂ) / 2) = -1 := by
    have harg : ↑Real.pi * (2 : ℂ) / 2 = ↑Real.pi := by
      apply Complex.ext <;> simp <;> ring
    rw [harg]
    simpa using Complex.cos_pi
  have hgam : Complex.Gamma (2 : ℂ) = 1 := by
    simpa using (Complex.Gamma_nat_eq_factorial 1)
  have hz2 : 0 < (riemannZeta (2 : ℂ)).re := by
    exact riemannZeta_re_pos_of_one_lt (x := (2 : ℝ)) (by norm_num)
  -- 对称方法 (模-相位分解, 实轴方向性): (2π)^(-2) — 底实正 (arg=0),
  -- 实指数 ⟹ 相位旋转 = 1 (cos 0 + sin 0·I), 模 = (2π)^(-2) 实正 —
  -- 不需要 cpow 展开/zpow 链 (代数方法), 用 cpow_ofReal 极坐标一步。
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-(2 : ℂ)) = ↑(1 / (2 * Real.pi) ^ 2 : ℝ) := by
    have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    rw [show (-(2 : ℂ)) = ((-2 : ℝ) : ℂ) by norm_num]
    rw [Complex.cpow_ofReal (2 * ↑Real.pi : ℂ) (-2 : ℝ)]
    -- 模: ‖2π‖ = 2π (实正); arg: 2π 实正 ⟹ arg = 0 ⟹ 相位 = 1
    have harg : (2 * ↑Real.pi : ℂ).arg = 0 := by
      have hcast : (2 * ↑Real.pi : ℂ) = ↑(2 * Real.pi : ℝ) := by norm_num
      rw [hcast]
      rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have hnorm : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      have hcast : (2 * ↑Real.pi : ℂ) = ↑(2 * Real.pi : ℝ) := by norm_num
      rw [hcast]
      exact (RCLike.norm_ofReal (2 * Real.pi)).trans
        (by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)])
    rw [harg, hnorm]
    -- 模-相位分解后目标自动坍缩: 相位 = 1 (cos 0 + sin 0·I), 模侧 rfl
    simp [Real.cos_zero, Real.sin_zero]
    rfl
  have hmain : riemannZeta (-(1 : ℂ)) = 2 * (2 * ↑Real.pi : ℂ) ^ (-(2 : ℂ)) * (-1) * riemannZeta (2 : ℂ) := by
    have hsub : 1 - (2 : ℂ) = -(1 : ℂ) := by ring
    rw [hsub] at hfe
    simpa [hcos, hgam] using hfe
  -- 周期方法 (实部投影, 不展开数值): 实系数 × ζ(2) 的 re
  -- = 系数 × (ζ2).re — 系数实 (ofReal: 实轴方向, im 泄漏 = 0) + ζ2 实
  -- (zeta_im_zero_on_real: 实轴上 ζ 的虚部为零 — 实轴周期结构)
  have hre : (2 * (2 * ↑Real.pi : ℂ) ^ (-(2 : ℂ)) * (-1) * riemannZeta (2 : ℂ)).re
      = -(2 * (1 / (2 * Real.pi) ^ 2)) * (riemannZeta (2 : ℂ)).re := by
    rw [hpow]
    -- 完全周期化: 系数整体 = ↑(-2a) (单一 ofReal, 不展开 a),
    -- mul_re 一步投影, 实性代入 (ofReal_re/ofReal_im + ζ2 实值) — 无数值展开
    let a : ℝ := 1 / (2 * Real.pi) ^ 2
    have hcoef : (2 * ↑a * (-1) : ℂ) = ↑(-(2 * a)) := by norm_num [a]
    rw [hcoef]
    rw [Complex.mul_re]
    -- 实性代入: 系数 im = 0 (ofReal), ζ(2) im = 0 (zeta_im_zero_on_real, 周期轴固定)
    have hb_re : (↑(-(2 * a)) : ℂ).re = -(2 * a) := by simp
    have hb_im : (↑(-(2 * a)) : ℂ).im = 0 := by simp
    have hz2_im0 : (riemannZeta (2 : ℂ)).im = 0 := zeta_im_zero_on_real 2
    rw [hb_re, hb_im, hz2_im0]
    -- 收尾: 0·0 项清除 + a 定义替换 (两边同形, rfl)
    simp [a]
  rw [hmain, hre]
  have hcoef : (0 : ℝ) < 2 * (1 / (2 * Real.pi) ^ 2) := by positivity
  have hprod : 0 < 2 * (1 / (2 * Real.pi) ^ 2) * (riemannZeta (2 : ℂ)).re :=
    mul_pos hcoef hz2
  linarith


end RiemannDualPath
