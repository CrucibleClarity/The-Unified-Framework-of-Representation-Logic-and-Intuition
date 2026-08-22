import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# 节点 06: 矩形闭合与边界估计 (Node 06: Rectangle Closure) — 双路径

## 本节点: 矩形四边的边界结构 (底边相位 0 + 右边模界)

同一结论的双路径 (矩形闭合的边界件):
- **[对称侧]** (态③): 底边 = 实轴 = 反射不动点 — ζ 在实轴实值
  (riemannZeta_conj 反射对称) ⟹ 底边相位 = 0。
- **[分析侧]** (态①②): 右边模界 — ζ(2+it) 级数绝对收敛,
  ‖ζ(2+it)‖ ≤ Σ n^{-2} (模 = 相位无关量, zeta_line_two_bounded)。

(翻转计数整数层 + 参数原理见 37 主文件/zeta_argument_iso。)
两段各自独立, 只 import Mathlib。

English: Node 06 — rectangle boundary components. Symmetry side:
bottom edge phase = 0 (ζ real on the real axis). Analysis side:
right-edge modulus bound ‖ζ(2+it)‖ ≤ ζ(2).
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
    [对称侧] (态③) — 底边 = 反射不动点 (相位 0)
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

/-! ============================================================
    [分析侧] (态①②) — 右边模界 (级数绝对收敛)
    ============================================================ -/

theorem zeta_line_two_bounded (t : ℝ) :
    ‖riemannZeta ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  -- ζ(2+it) = Σ n^{-2-it} (Re = 2 > 1 级数)
  rw [zeta_eq_tsum_one_div_nat_cpow (s := (2 : ℂ) + (t : ℂ) * Complex.I) (by norm_num)]
  -- ‖Σ‖ ≤ Σ‖·‖ (norm_tsum_le_tsum_norm): 需绝对收敛
  have hterm : ∀ n : ℕ, ‖(n : ℂ) ^ (-(2 : ℂ) - (t : ℂ) * Complex.I)‖ = (n : ℝ) ^ (-2 : ℝ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      -- 0^{-2-it} = 0, ‖0‖ = 0 = 0^{-2} (rpow 0^y = 0 当 y ≠ 0)
      have hz : -(2 : ℂ) - (t : ℂ) * Complex.I ≠ 0 := by
        intro h
        have hre : (-(2 : ℂ) - (t : ℂ) * Complex.I).re = 0 := by rw [h]; simp
        norm_num at hre
      rw [Nat.cast_zero]
      rw [Complex.zero_cpow hz]
      norm_num
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [Complex.cpow_def_of_ne_zero hn0]
      rw [Complex.norm_exp]
      -- log(↑n) = ↑(log n) (正实数)
      have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast]
        rw [← Complex.ofReal_log (Nat.cast_nonneg n)]
      -- (-2 - i·t)·log(↑n) 的实部 = -2·log n
      have hre : (((-(2 : ℂ) - (t : ℂ) * Complex.I) * Complex.log (n : ℂ)).re)
          = -2 * Real.log (n : ℝ) := by
        have hlog_re : (Complex.log (n : ℂ)).re = Real.log (n : ℝ) := by
          rw [← Complex.ofReal_natCast]
          have hl := Complex.ofReal_log (Nat.cast_nonneg n)
          rw [← hl]
          rfl
        have hlog_im : (Complex.log (n : ℂ)).im = 0 := by
          rw [← Complex.ofReal_natCast]
          have hl := Complex.ofReal_log (Nat.cast_nonneg n)
          rw [← hl]
          rfl
        rw [Complex.mul_re]
        simp only [Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im]
        rw [hlog_re, hlog_im]
        norm_num
      rw [mul_comm, hre]
      -- exp(-2·log n) = n^{-2} (rpow 定义)
      rw [Real.rpow_def_of_pos hpos]
      congr 1
      ring
  have hconv : ∀ n : ℕ, 1 / (n : ℂ) ^ (2 + (t : ℂ) * Complex.I)
      = (n : ℂ) ^ (-(2 : ℂ) - (t : ℂ) * Complex.I) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hz1 : (2 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
        intro h
        have : ((2 : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h]; simp
        norm_num at this
      have hz2 : (-(2 : ℂ) - (t : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have : ((-(2 : ℂ) - (t : ℂ) * Complex.I).re) = 0 := by rw [h]; simp
        norm_num at this
      rw [Nat.cast_zero]
      rw [Complex.zero_cpow hz1, Complex.zero_cpow hz2]
      simp
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [one_div, ← Complex.cpow_neg]
      congr 1
      ring
  have hsum_norm : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ (2 + (t : ℂ) * Complex.I)‖) := by
    -- ‖1/n^{2+it}‖ = ‖n^{-2-it}‖ = n^{-2}, Σ n^{-2} 收敛 (p = -2 < -1)
    have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
      (Real.summable_nat_rpow (p := (-2 : ℝ))).2 (by norm_num)
    refine hsum.congr ?_
    intro n
    rw [hconv n]
    exact (hterm n).symm
  exact (norm_tsum_le_tsum_norm hsum_norm).trans_eq (by
    apply tsum_congr
    intro n
    rw [hconv n]
    exact hterm n)



end RiemannDualPath
