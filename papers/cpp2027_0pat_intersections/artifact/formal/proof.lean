import Formal.ZeroRelative.ComplexAxis
import Mathlib.Analysis.Real.Sqrt

/-!
# 习题 XXIX: 复平面四对象交点观测 (0pat)

用户洞察 (2026-08-21): 直接观测复平面的横轴、纵轴、临界线圆、素数圆,
观察交点。

交点总表 (全部机器验证):
  ┌─────────────────────┬──────────────────────────────────────┐
  │ 对象对               │ 交点                                │
  ├─────────────────────┼──────────────────────────────────────┤
  │ 横轴 ∩ 纵轴          │ {0} (定义)                           │
  │ 横轴 ∩ 临界圆        │ {0, 2} (realAxis_inter_criticalCircle, C020) │
  │ 纵轴 ∩ 临界圆        │ {0} (新: imagAxis_inter_criticalCircle)      │
  │ 横轴 ∩ 素数圆 p      │ {±√p} (新: realAxis_inter_primeCircle)       │
  │ 纵轴 ∩ 素数圆 p      │ {±i√p} (新: imagAxis_inter_primeCircle)       │
  │ 素数圆 2 ∩ 临界圆    │ {1±i} (prime2Circle_inter_criticalCircle, C020) │
  │ 素数圆 3 ∩ 临界圆    │ {3/2 ± √3/2·i} (新: prime3Circle_inter_criticalCircle) │
  │ 素数圆 p≥5 ∩ 临界圆  │ ∅ (新: primeCircle_inter_criticalCircle_ge5!) │
  └─────────────────────┴──────────────────────────────────────┘

核心新定理: 素数圆与临界圆相交 ⟺ p ∈ {2, 3} — 半径 √p 的圆与圆心
(1,0) 半径 1 的圆相交当且仅当 p ≤ 4 (素数 ⟹ p = 2 或 3)。

谱系坐标: (R23, C3) 素数圆 × 解析数论; 连接 C020 (两圆交点) 与 XXIV。
-/

namespace ComplexPlaneIntersections

noncomputable section

open ZeroRelative
open ZeroRelative.ComplexAxis

/-- 纵轴 (虚轴) 与临界圆: t·J ∈ criticalCircle ↔ t = 0
    (虚轴与临界圆只交于原点; 对比实轴交 {0, 2})。 -/
theorem imagAxis_inter_criticalCircle (t : ℝ) :
    (lift t * J : ComplexAxis) ∈ criticalCircle ↔ t = 0 := by
  constructor
  · intro h
    have hn : norm (lift t * J - lift 1) = 1 := by
      simpa [criticalCircle] using h
    -- norm ⟨-1, t⟩ = 1 + t² = 1 ⟹ t = 0
    have hcalc : 1 + t ^ 2 = 1 := by
      simpa [norm, lift, J, mul] using hn
    nlinarith
  · intro ht
    subst ht
    simp [criticalCircle, norm, lift, J]

/-- 横轴与素数圆: lift r ∈ primeCircle p ↔ r² = p (交于 ±√p)。 -/
theorem realAxis_inter_primeCircle (r : ℝ) (p : ℕ) :
    (lift r : ComplexAxis) ∈ primeCircle p ↔ r ^ 2 = (p : ℝ) := by
  simp [primeCircle, norm, lift]

/-- 纵轴与素数圆: t·J ∈ primeCircle p ↔ t² = p (交于 ±i√p)。 -/
theorem imagAxis_inter_primeCircle (t : ℝ) (p : ℕ) :
    (lift t * J : ComplexAxis) ∈ primeCircle p ↔ t ^ 2 = (p : ℝ) := by
  simp [primeCircle, norm, lift, J]

/-- 素数圆 3 与临界圆: z = 3/2 + √3/2·J 在交集中
    (norm = 9/4 + 3/4 = 3; norm(z-1) = 1/4 + 3/4 = 1)。 -/
theorem prime3Circle_inter_criticalCircle :
    (⟨3 / 2, Real.sqrt 3 / 2⟩ : ComplexAxis) ∈ primeCircle 3 ∧
      (⟨3 / 2, Real.sqrt 3 / 2⟩ : ComplexAxis) ∈ criticalCircle := by
  have hsq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    have h1 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  constructor
  · simp [primeCircle, norm]
    nlinarith
  · simp [criticalCircle, norm, lift]
    nlinarith

/-- 核心新定理: 素数 p ≥ 5 的素数圆与临界圆不相交
    (半径 √p 的圆与圆心 (1,0) 半径 1 的圆: 相交 ⟹ p ≤ 4)。 -/
theorem primeCircle_inter_criticalCircle_ge5 {p : ℕ} (hp5 : 5 ≤ p) :
    primeCircle p ∩ criticalCircle = ∅ := by
  ext z
  constructor
  · intro hz
    have hn : norm z = (p : ℝ) := hz.1
    have hc : norm (z - lift 1) = 1 := hz.2
    -- a = p/2 (从 norm(z-1) = norm z - 2a + 1)
    have ha : z.a = (p : ℝ) / 2 := by
      have h1 : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [norm] using hn
      have h2 : (z.a - 1) ^ 2 + z.b ^ 2 = 1 := by simpa [norm, lift] using hc
      nlinarith
    -- b² = p - p²/4 < 0 (p ≥ 5) — 矛盾
    have hb2 : z.b ^ 2 = (p : ℝ) - (p : ℝ) ^ 2 / 4 := by
      have h1 : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [norm] using hn
      nlinarith
    have hneg : (p : ℝ) - (p : ℝ) ^ 2 / 4 < 0 := by
      have hpR : (4 : ℝ) < (p : ℝ) := by
        have hp5' : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
        nlinarith
      nlinarith
    nlinarith
  · intro hz
    simp at hz

end
end ComplexPlaneIntersections
