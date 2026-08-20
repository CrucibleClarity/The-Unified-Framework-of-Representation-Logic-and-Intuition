/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Formal.ZeroRelative.NatSource

/-!
# Complex axis by projection (真复数轴)

docs/关于黎曼猜想的思考.md 的假设: 复数轴是某高维结构中 "-1" 在人类数学
空间 (实数轴) 的投影; 根号 = 投影的逆。本文件按此假设构造 (DEFINITION +
OBSERVATION / KNOWN: 标准 ℂ 构造的旋转-矩阵表示, 非新结构)。

高维结构 = 二维旋转代数 `ComplexAxis`, 元素 a + bJ:
  * 标量部分 a ∈ ℝ — 投影后幸存, 落在数轴上;
  * 旋转部分 b·J — 90° 旋转 J, J² = -1, 投影后丢失。
乘法 = 复数乘法 (a₁+b₁J)(a₂+b₂J) = (a₁a₂-b₁b₂) + (a₁b₂+a₂b₁)J。

构造内容:
  1. J² = -1: 高维中 -1 有平方根 (w = J), 即 √(-1) 在投影前存在。
  2. 投影 π(a+bJ) = a 保加法, 但不保乘法:
     π(J·J) = -1 ≠ π(J)·π(J) = 0 — 开方/旋转信息在投影中丢失。
  3. 根号构造: 实数轴上 -1 无平方根 (∀ t, t² ≠ -1); 抬升 lift 到高维后
     开方可行 — √ 是"投影的逆"。
  4. lift 保加法与乘法: 实数轴作为标量部分嵌入高维结构是环同态。
-/

namespace ZeroRelative

/-- 高维结构: 二维旋转代数 a + b·J (矩阵表示 [[a,-b],[b,a]], ≅ ℂ)。 -/
structure ComplexAxis where
  a : ℝ
  b : ℝ

namespace ComplexAxis

/-- 加法 (分量) -/
def add (x y : ComplexAxis) : ComplexAxis := ⟨x.a + y.a, x.b + y.b⟩

/-- 相反数 -/
def neg (x : ComplexAxis) : ComplexAxis := ⟨-x.a, -x.b⟩

/-- 零 -/
def zero : ComplexAxis := ⟨0, 0⟩

/-- 乘性单位 1 -/
def one : ComplexAxis := ⟨1, 0⟩

/-- 90° 旋转 J: 高维结构中 "-1 的平方根" -/
def J : ComplexAxis := ⟨0, 1⟩

/-- 复数乘法: (a₁+b₁J)(a₂+b₂J) = (a₁a₂-b₁b₂) + (a₁b₂+a₂b₁)J -/
def mul (x y : ComplexAxis) : ComplexAxis :=
  ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a⟩

instance : Add ComplexAxis := ⟨add⟩
instance : Neg ComplexAxis := ⟨neg⟩
instance : Sub ComplexAxis := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Zero ComplexAxis := ⟨zero⟩
instance : One ComplexAxis := ⟨one⟩
instance : Mul ComplexAxis := ⟨mul⟩

/-- 结构外延: 分量相等 ⟹ 元素相等 (注册给 `ext` 策略)。 -/
@[ext]
theorem ext (x y : ComplexAxis) (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x <;> cases y <;> simp_all

/-- 分量 simp 定理: 加法/减法/乘法/单位/零的分量展开。 -/
@[simp] theorem add_apply_a (x y : ComplexAxis) : (x + y).a = x.a + y.a := by rfl
@[simp] theorem add_apply_b (x y : ComplexAxis) : (x + y).b = x.b + y.b := by rfl
@[simp] theorem sub_apply_a (x y : ComplexAxis) : (x - y).a = x.a - y.a := by rfl
@[simp] theorem sub_apply_b (x y : ComplexAxis) : (x - y).b = x.b - y.b := by rfl
@[simp] theorem mul_apply_a (x y : ComplexAxis) : (x * y).a = x.a * y.a - x.b * y.b := by rfl
@[simp] theorem mul_apply_b (x y : ComplexAxis) : (x * y).b = x.a * y.b + x.b * y.a := by rfl
@[simp] theorem one_apply_a : (1 : ComplexAxis).a = 1 := by rfl
@[simp] theorem one_apply_b : (1 : ComplexAxis).b = 0 := by rfl
@[simp] theorem zero_apply_a : (0 : ComplexAxis).a = 0 := by rfl
@[simp] theorem zero_apply_b : (0 : ComplexAxis).b = 0 := by rfl

/-- J² = -1: 在高维结构中, -1 有平方根 (w = J)。 -/
theorem J_sq : J * J = (-1 : ComplexAxis) := by
  change mul J J = neg one
  ext <;> simp [J, mul, one, neg] <;> norm_num

/-- 抬升: 把数轴上的点放入高维结构 (旋转分量为 0)。 -/
def lift (t : ℝ) : ComplexAxis := ⟨t, 0⟩

@[simp] theorem lift_apply_a (t : ℝ) : (lift t).a = t := by rfl
@[simp] theorem lift_apply_b (t : ℝ) : (lift t).b = 0 := by rfl

/-- 投影: 取标量部分, 旋转信息丢失 (π(a+bJ) = a)。 -/
def proj (x : ComplexAxis) : ℝ := x.a

/-- 投影保加法。 -/
theorem proj_add (x y : ComplexAxis) : proj (x + y) = proj x + proj y := by
  rfl

/-- 投影把 J 压成 0: 旋转信息在投影中丢失。 -/
theorem proj_J : proj J = 0 := by
  rfl

/-- 抬升后投影还原: π(lift t) = t。 -/
theorem proj_lift (t : ℝ) : proj (lift t) = t := by
  rfl

/-- lift 保加法: 实数轴嵌入高维结构是同态 (加法部分)。 -/
theorem lift_add (x y : ℝ) : lift (x + y) = lift x + lift y := by
  change lift (x + y) = add (lift x) (lift y)
  ext <;> simp [lift, add] <;> norm_num

/-- lift 保乘法: 实数轴嵌入高维结构是同态 (乘法部分)。 -/
theorem lift_mul (x y : ℝ) : lift (x * y) = lift x * lift y := by
  change lift (x * y) = mul (lift x) (lift y)
  ext <;> simp [lift, mul] <;> ring

/-- 投影不保乘法: π(J·J) = -1 ≠ π(J)·π(J) = 0。开方/旋转信息在投影中丢失,
即"结构丢失"定理: 高维里的等式 w·w = -1 在投影下不封闭。 -/
theorem proj_mul_not_preserved : proj (J * J) ≠ proj J * proj J := by
  change (mul J J).a ≠ J.a * J.a
  norm_num [J, mul]

/-- 高维结构中 -1 有平方根: w = J 满足 w·w = -1。 -/
theorem sqrt_neg_one_exists_high : ∃ w : ComplexAxis, w * w = (-1 : ComplexAxis) :=
  ⟨J, J_sq⟩

/-- 投影到实数轴后, -1 无平方根: ∀ t : ℝ, t·t ≠ -1。
"根号构造"的反向: 数轴上的 -1 无法开方, 必须经抬升到高维结构才可行。 -/
theorem sqrt_neg_one_not_exists_axis (t : ℝ) : t * t ≠ -1 := by
  nlinarith [sq_nonneg t]

/-- 根号 = 投影的逆: 抬升后的 -1 (lift (-1)) 在高维中开方得 J。 -/
theorem lift_neg_one_sqrt : J * J = lift (-1) := by
  change mul J J = lift (-1)
  ext <;> simp [J, mul, lift] <;> norm_num

/-! ## Drifted basepoint: 自然数在复数轴上, λ 基点漂移到 i

docs/关于黎曼猜想的思考.md: 复平面上定义自然数 ⟹ λ 基点落在复数轴上,
不再是原点 0, 而是 i 的某种变换。投影视角 (OBSERVATION/KNOWN):
  * 基点 i 被投影显示为 0 — "原点假象": 投影视角下自然数看似从原点出发,
    实际基点在 i, 基点真实位置被投影丢失 (与 J 丢失同机制);
  * i 的变换族 (纯虚数 ⟨0,b⟩) 投影都显示 0;
  * 后继 σ(x) = x + 1 (实轴方向平移) 在投影下是实数轴的 +1: 投影把漂移
    链条 Chain(succ, i) 整体映成自然数结构候选 (含 0, 对 +1 封闭);
  * 基点漂移在投影下不可观测: 任何纯虚基点给出同一投影结构。 -/

/-- 虚数单位 i: 高维结构中 -1 的平方根 (90° 旋转 J)。 -/
def i : ComplexAxis := J

/-- 后继: 沿实轴方向平移 1: σ(x) = x + 1。 -/
def succ (x : ComplexAxis) : ComplexAxis := x + 1

/-- 漂移基点: i (不是原点 0)。 -/
def basepoint : ComplexAxis := i

/-- 漂移链条: Chain(succ, i) — 最小 σ-闭结构, 无 Nat primitive。 -/
def driftChain : Set ComplexAxis := Chain succ basepoint

/-- 原点假象: 基点 i 的投影显示为 0。投影视角下自然数看似从原点出发,
实际基点在 i — 基点真实位置被投影丢失。 -/
theorem basepoint_proj : proj basepoint = 0 := by
  rfl

/-- i 的变换族: 所有纯虚基点 ⟨0, b⟩ (b·J) 的投影都显示为 0 —
"i 的某种变换"在投影下都伪装成原点。 -/
theorem pure_imag_proj (b : ℝ) : proj (⟨0, b⟩ : ComplexAxis) = 0 := by
  rfl

/-- 后继在投影下是实数轴的 +1: π(σ(x)) = π(x) + 1。 -/
theorem proj_succ (x : ComplexAxis) : proj (succ x) = proj x + 1 := by
  unfold succ
  rfl

/-- 投影链条含原点: 0 ∈ π(Chain(succ, i)) — 投影后自然数结构从 0 开始。 -/
theorem zero_in_proj_chain : (0 : ℝ) ∈ proj '' driftChain := by
  refine ⟨basepoint, ?_, ?_⟩
  · exact chain_mem_self succ basepoint
  · exact basepoint_proj

/-- 投影链条对 +1 封闭: π(Chain(succ, i)) 是实数轴上的后继闭结构 —
投影把漂移链条整体映成自然数结构候选 (σ': r ↦ r+1)。 -/
theorem proj_chain_succ_closed :
    ∀ y : ℝ, y ∈ proj '' driftChain → y + 1 ∈ proj '' driftChain := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨succ x, ?_, ?_⟩
  · exact chain_closed succ basepoint x hx
  · exact proj_succ x

/-- 基点漂移在投影下不可观测: 任何纯虚基点 e (proj e = 0, 即 i 的某种变换)
的链条, 投影后都得到同样的结构: 含 0 且对 +1 封闭。 -/
theorem proj_chain_basepoint_independent (e : ComplexAxis) (he : proj e = 0) :
    (0 : ℝ) ∈ proj '' Chain succ e ∧
      ∀ y : ℝ, y ∈ proj '' Chain succ e → y + 1 ∈ proj '' Chain succ e := by
  constructor
  · refine ⟨e, chain_mem_self succ e, he⟩
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨succ x, chain_closed succ e x hx, proj_succ x⟩

/-! ## 实数轴的可疑性: 它只是另一根被压扁的复数轴

投影视角下的"实数轴" = 过纯虚基点 ⟨0,b⟩ 的实方向线 {⟨0,b⟩ + t·1}。关键
观测 (OBSERVATION/KNOWN):
  * 过任意纯虚点的实方向线, 投影都是完整 ℝ — 且投影在线上是双射 (每根
    线上的点恰好由投影值标定);
  * 因此"实数轴"的位置 (过 0 还是过 i、过 b₁·J 还是 b₂·J) 在投影下
    不可区分 — 它不是结构事实, 只是投影等价类;
  * 实数轴 = axisLine 0, 与过 i 的线投影相同: 它只是 ComplexAxis 里
    无数"同样像数轴"的线之一, 本质上是一根被投影压扁的复数轴。 -/

/-- 过纯虚基点 ⟨0, b⟩ 的实方向线: {⟨0,b⟩ + t·1 : t ∈ ℝ}。 -/
def axisLine (b : ℝ) : Set ComplexAxis :=
  Set.range (fun t : ℝ => ⟨0, b⟩ + lift t)

/-- 实数轴 = 过原点 0 的实方向线。 -/
def realAxis : Set ComplexAxis := axisLine 0

/-- 线上点的投影: π(⟨0,b⟩ + lift t) = t — 线上的点恰好由投影值标定。 -/
theorem axisLine_eval_proj (b t : ℝ) : proj (⟨0, b⟩ + lift t) = t := by
  rw [proj_add, pure_imag_proj, proj_lift, zero_add]

/-- 投影覆盖整条线: 每个实数 r 都是线上某点的投影。 -/
theorem axisLine_proj_all (b r : ℝ) : r ∈ proj '' axisLine b := by
  refine ⟨⟨0, b⟩ + lift r, ⟨r, rfl⟩, ?_⟩
  exact axisLine_eval_proj b r

/-- 投影在线上单射: 线上不同的点给出不同的投影值 (线没有塌缩)。 -/
theorem axisLine_proj_injective (b : ℝ) :
    ∀ ⦃x y : ComplexAxis⦄, x ∈ axisLine b → y ∈ axisLine b →
      proj x = proj y → x = y := by
  intro x y hx hy hxy
  rcases hx with ⟨t1, rfl⟩
  rcases hy with ⟨t2, rfl⟩
  have ht1 : proj (⟨0, b⟩ + lift t1) = t1 := axisLine_eval_proj b t1
  have ht2 : proj (⟨0, b⟩ + lift t2) = t2 := axisLine_eval_proj b t2
  have ht : t1 = t2 := by
    calc
      t1 = proj (⟨0, b⟩ + lift t1) := ht1.symm
      _ = proj (⟨0, b⟩ + lift t2) := hxy
      _ = t2 := ht2
  rw [ht]

/-- 投影把整条线映成全部实数: proj '' axisLine b = ℝ。 -/
theorem axisLine_proj_eq_univ (b : ℝ) : proj '' axisLine b = Set.univ := by
  ext r
  constructor
  · intro _; trivial
  · intro _; exact axisLine_proj_all b r

/-- 投影在实方向线上是完整一根轴: ℝ ≃ axisLine b。 -/
def axisProjEquiv (b : ℝ) : ℝ ≃ {x : ComplexAxis // x ∈ axisLine b} where
  toFun t := ⟨⟨0, b⟩ + lift t, ⟨t, rfl⟩⟩
  invFun x := proj x.1
  left_inv t := by
    exact axisLine_eval_proj b t
  right_inv x := by
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨t, rfl⟩
    apply Subtype.ext
    change ⟨0, b⟩ + lift (proj (⟨0, b⟩ + lift t)) = ⟨0, b⟩ + lift t
    rw [axisLine_eval_proj b t]

/-- 实数轴位置不可观测: 过任意两个纯虚基点的实方向线, 投影都是同一根
完整实数轴 — "实数轴"的位置不是结构事实, 只是投影等价类。 -/
theorem axisLine_proj_independent (b1 b2 : ℝ) :
    proj '' axisLine b1 = proj '' axisLine b2 := by
  rw [axisLine_proj_eq_univ b1, axisLine_proj_eq_univ b2]

/-- 实数轴 (axisLine 0) 与过 i 的线 (axisLine 1) 投影相同: 那根"数轴"
只是无数同样像数轴的线之一 — 假复数轴。 -/
theorem realAxis_indistinguishable_from_i_line :
    proj '' realAxis = proj '' axisLine 1 := by
  exact axisLine_proj_independent 0 1

/-! ## 反演的基点漂移 (复平面内)

黎曼函数的反演方向 (docs/关于黎曼猜想的思考.md: "黎曼函数就有反演的结构",
ζ(s) = Σ 1/n^s 每项都是取倒数 — 反演) 在复平面 ComplexAxis 内形式化:
  * recip: 复反演 (取倒数) inv z = conj z / |z|², 是乘法逆 (z ≠ 0);
  * 实轴上的反演 = 实数倒数 (recip_lift);
  * 反演不保投影 (基点不漂移视角): π(recip z) ≠ 1/π(z) — 投影下反演信息丢失;
  * circleInv: 基点漂移反演 (球心 c, 半径 r): I_{c,r}(z) = c + r²·recip(conj z - c)
    — 标准反演的基点漂移版本;
  * 保投影: 球面 |z-c| = r 上的点在漂移反演下不动 ⟹ 投影保持 (保投影又保对称);
  * 平移 = 基点漂移: 平移共轭移动反演球心 (circleInv_translate) —
    平移与反演本质上是同一结构 (基点漂移), 不是两个独立结构。

★ 蜷曲性说明: 本节的漂移反演是在 ComplexAxis (投影构造的假复数轴, 基点
不漂移、轴不蜷曲的简化视角) 内部做的 — 它本质上是"假复数轴的反演漂移",
同样蜷曲。真正的保投影反演需要穿出复平面的漂移 (球心在实轴 (1,0) 的球面
结构), 待更高维构造。 -/

/-- 共轭: conj(a + bJ) = a - bJ。 -/
def conj (z : ComplexAxis) : ComplexAxis := ⟨z.a, -z.b⟩

@[simp] theorem conj_apply_a (z : ComplexAxis) : (conj z).a = z.a := by rfl
@[simp] theorem conj_apply_b (z : ComplexAxis) : (conj z).b = -z.b := by rfl

/-- 反演 (取倒数): recip z = conj z / |z|² — 复平面中的反演。 -/
noncomputable def recip (z : ComplexAxis) : ComplexAxis :=
  ⟨z.a / (z.a ^ 2 + z.b ^ 2), -z.b / (z.a ^ 2 + z.b ^ 2)⟩

@[simp] theorem recip_apply_a (z : ComplexAxis) : (recip z).a = z.a / (z.a ^ 2 + z.b ^ 2) := by rfl
@[simp] theorem recip_apply_b (z : ComplexAxis) : (recip z).b = -z.b / (z.a ^ 2 + z.b ^ 2) := by rfl

/-- 反演是乘法逆: z ≠ 0 → z * recip z = 1。 -/
theorem recip_mul_self (z : ComplexAxis) (hz : z ≠ 0) : z * recip z = 1 := by
  cases z with
  | mk a b =>
    have hsq : a ^ 2 + b ^ 2 ≠ 0 := by
      intro h
      apply hz
      ext
      · have ha2 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
        exact sq_eq_zero_iff.mp ha2
      · have hb2 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
        exact sq_eq_zero_iff.mp hb2
    ext
    · simp [recip]
      field_simp [hsq]
      ring
    · simp [recip]
      field_simp [hsq]
      ring

/-- 实轴上的反演 = 实数倒数: recip (lift a) = lift (1/a)。 -/
theorem recip_lift (a : ℝ) (ha : a ≠ 0) : recip (lift a) = lift (1 / a) := by
  ext
  · simp [recip, lift]
    field_simp [ha]
  · simp [recip, lift]

/-- 反演不保投影 (基点不漂移视角): π(recip z) ≠ 1/π(z) 当旋转分量存在 —
投影下反演信息丢失。 -/
theorem proj_recip_lost : proj (recip (⟨1, 1⟩ : ComplexAxis)) ≠ 1 / proj ⟨1, 1⟩ := by
  norm_num [recip, proj]

/-- 基点漂移反演 (球心 c, 半径 r): I_{c,r}(z) = c + r²·recip(conj z - c) —
标准反演 (球心 0, 半径 1) 的基点漂移版本。 -/
noncomputable def circleInv (c : ComplexAxis) (r : ℝ) (z : ComplexAxis) : ComplexAxis :=
  c + lift (r ^ 2) * recip (conj z - c)

/-- 漂移核心: |w|² = r² 时 r²·recip(conj w) = w — 球面半径与点长度的互换。 -/
theorem circleInv_core (w : ComplexAxis) (r : ℝ) (hw : w ≠ 0)
    (h : w.a ^ 2 + w.b ^ 2 = r ^ 2) :
    lift (r ^ 2) * recip (conj w) = w := by
  have hsq : w.a ^ 2 + w.b ^ 2 ≠ 0 := by
    intro h
    apply hw
    ext
    · have ha2 : w.a ^ 2 = 0 := by nlinarith [sq_nonneg w.a, sq_nonneg w.b, h]
      exact sq_eq_zero_iff.mp ha2
    · have hb2 : w.b ^ 2 = 0 := by nlinarith [sq_nonneg w.a, sq_nonneg w.b, h]
      exact sq_eq_zero_iff.mp hb2
  ext
  · simp [recip, conj, lift]
    rw [← h]
    field_simp [hsq]
  · simp [recip, conj, lift]
    rw [← h]
    field_simp [hsq]

/-- 球面上的点在漂移反演下不动 (球心在实数轴上): |z - c| = r → I_{c,r}(z) = z —
基点漂移视角下反演保投影 (又保对称)。 -/
theorem circleInv_fixed (c : ComplexAxis) (r : ℝ) (z : ComplexAxis)
    (hc : c.b = 0) (hz : z ≠ c) (h : (z - c).a ^ 2 + (z - c).b ^ 2 = r ^ 2) :
    circleInv c r z = z := by
  unfold circleInv
  let w := z - c
  have hw0 : w ≠ 0 := by
    intro hw
    apply hz
    have : z - c = 0 := by simpa [w] using hw
    ext
    · have ha : (z - c).a = 0 := congrArg ComplexAxis.a this
      change z.a - c.a = 0 at ha
      linarith
    · have hb : (z - c).b = 0 := congrArg ComplexAxis.b this
      change z.b - c.b = 0 at hb
      linarith
  have hcore := circleInv_core w r hw0 (by simpa [w] using h)
  have hconj : conj z - c = conj (z - c) := by
    ext
    · change z.a - c.a = z.a - c.a
      rfl
    · change -z.b - c.b = -(z.b - c.b)
      rw [hc]
      ring
  rw [hconj]
  calc
    c + lift (r ^ 2) * recip (conj (z - c)) = c + lift (r ^ 2) * recip (conj w) := by rfl
    _ = c + w := by
      congr 1
    _ = z := by
      ext <;> simp [w] <;> ring

/-- 球面不动 ⟹ 投影保持: |z-c| = r → π(I_{c,r}(z)) = π(z) — 漂移视角下
反演保投影。 -/
theorem circleInv_proj_preserved (c : ComplexAxis) (r : ℝ) (z : ComplexAxis)
    (hc : c.b = 0) (hz : z ≠ c) (h : (z - c).a ^ 2 + (z - c).b ^ 2 = r ^ 2) :
    proj (circleInv c r z) = proj z := by
  rw [circleInv_fixed c r z hc hz h]

/-- 平移 = 基点漂移: 平移共轭移动反演球心 (平移向量在实轴上) —
I_{c+d,r}(z) = I_{c,r}(z-d) + d: 平移与反演本质是同一结构 (基点漂移)。 -/
theorem circleInv_translate (c d : ComplexAxis) (r : ℝ) (z : ComplexAxis)
    (hd : d.b = 0) :
    circleInv (c + d) r z = circleInv c r (z - d) + d := by
  unfold circleInv
  change c + d + lift (r ^ 2) * recip (conj z - (c + d)) =
    c + lift (r ^ 2) * recip (conj (z - d) - c) + d
  have hconj : conj z - (c + d) = conj (z - d) - c := by
    ext
    · simp <;> ring
    · simp
      rw [hd]
      ring
  rw [hconj]
  ext <;> simp <;> ring

/-! ## 黎曼函数的方向: 反演分量的求和

站在球面 (基点漂移) 视角, 反演结构 1/a + 1/b 的两项只是漂移的不同分量。
黎曼函数的构造 = 把分量调试到 1/n^s: ζ(s) = Σ 1/n^s 是反演分量的求和
(OBSERVATION/KNOWN; s = 1 时即调和级数部分和 1/1 + 1/2 + ... + 1/N,
"1/a + 1/b" 是其两分量情形):
  * npow: 自然数次幂 (递归, 无 Monoid 依赖);
  * zetaTerm n s = 1/(n+1)^s: 黎曼方向的分量 (整数反演的 s 次幂);
  * 分量在实轴上: zetaTerm n s = lift (1/(n+1)^s) — 投影视角下是可观测的
    实数位置;
  * zetaPartial N s = Σ_{k=1}^{N+1} 1/k^s: 反演分量的部分和;
  * ζ_0(s) = 1, ζ_1(1) = 1/1 + 1/2 (两分量情形)。 -/

/-- 自然数次幂 (递归, 无 Monoid 依赖): z⁰ = 1, z^{s+1} = z^s · z。 -/
def npow (z : ComplexAxis) : ℕ → ComplexAxis
  | 0 => 1
  | s + 1 => npow z s * z

/-- 1 的幂: 1^s = 1。 -/
theorem npow_one (s : ℕ) : npow 1 s = 1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
      change npow 1 s * 1 = 1
      rw [ih]
      ext <;> norm_num

/-- 抬升与幂交换: (lift n)^s = lift (n^s) — 实数整数幂在抬升下保持。 -/
theorem npow_lift (n s : ℕ) : npow (lift n) s = lift ((n : ℝ) ^ s) := by
  induction s with
  | zero => ext <;> simp [npow, lift]
  | succ s ih =>
      change npow (lift n) s * lift n = lift ((n : ℝ) ^ (s + 1))
      rw [ih]
      rw [← lift_mul]
      congr 1

/-- 1 的反演: recip 1 = 1。 -/
theorem recip_one : recip 1 = 1 := by
  ext <;> simp [recip] <;> norm_num

/-- 黎曼方向的分量: 1/(n+1)^s — 整数 (n+1) 的反演 s 次幂 (漂移分量)。
在"反演漂移轴"(用户俗称: 瞎tm反演轴)上, 分量 = 整数位取反演。 -/
noncomputable def zetaTerm (n s : ℕ) : ComplexAxis :=
  recip (npow (lift (n + 1 : ℕ)) s)

/-- 黎曼部分和: ζ_N(s) = Σ_{k=1}^{N+1} 1/k^s — 沿反演漂移轴数整数位
1,2,3,..., 每位取反演分量 1/k^s 求和; "级数收敛" = 数到无穷时和停住。 -/
noncomputable def zetaPartial : ℕ → ℕ → ComplexAxis
  | 0, s => zetaTerm 0 s
  | N + 1, s => zetaPartial N s + zetaTerm (N + 1) s

/-- 分量是实数轴上的位置: 1/(n+1)^s = lift (1/(n+1)^s) — 投影视角下
每个漂移分量都是可观测的实数位置。 -/
theorem zetaTerm_lift (n s : ℕ) : zetaTerm n s = lift ((1 : ℝ) / (((n + 1 : ℕ) ^ s) : ℝ)) := by
  unfold zetaTerm
  rw [npow_lift (n + 1) s]
  have hne : (((n + 1 : ℕ) : ℝ) ^ s) ≠ 0 := by
    rw [← Nat.cast_pow]
    exact_mod_cast (pow_ne_zero s (by omega : n + 1 ≠ 0))
  rw [recip_lift _ hne]

/-- ζ 的第一项: ζ_0(s) = 1/1^s = 1。 -/
theorem zetaPartial_zero (s : ℕ) : zetaPartial 0 s = 1 := by
  unfold zetaPartial zetaTerm
  rw [npow_lift (0 + 1) s]
  simp [one_pow]
  rw [recip_lift 1 (by norm_num)]
  ext <;> norm_num [lift]

/-- 反演对偶接入黎曼方向: ζ 的两分量部分和 (s=1) = 1/1 + 1/2 —
"1/a + 1/b" 正是黎曼部分和的 s=1 两分量情形 (球面视角: 两个漂移分量)。 -/
theorem zeta_two_terms : zetaPartial 1 1 = lift 1 + lift (1 / 2) := by
  unfold zetaPartial
  change zetaTerm 0 1 + zetaTerm 1 1 = lift 1 + lift (1 / 2)
  unfold zetaTerm
  rw [npow_lift (0 + 1) 1, npow_lift (1 + 1) 1]
  norm_num
  rw [recip_lift 1 (by norm_num), recip_lift 2 (by norm_num)]
  norm_num [lift]

/-! ## 黎曼临界线: 1/2 = 反演-平移对偶的对称中心

非平凡零点 Re(s) = 1/2 的 1/2 不是随便的位置: 它是映射 s ↦ 1-s 的
唯一不动点 (实数轴), 即"平移-反演对偶" a + b = 1 的对称中心 — 正是
C012 inversion_dual_position 在临界条件 x + y = 1 下的特例。
(OBSERVATION/KNOWN: 函数方程 ξ(s) = ξ(1-s) 的对称轴。)

关键定理 (Lean-verified):
  * one_minus_fixed / one_minus_fixed_cplx: s = 1-s 的唯一解是 1/2;
  * critical_line_iff_conj: Re(s) = 1/2 ⟺ 1 - s = conj s — 临界线上
    1-s 与 s 互为共轭 (函数方程对称 + 实系数共轭对称的组合);
  * one_minus_proj: 函数方程映射 s ↦ 1-s 在投影下是实轴反射 π(1-s) = 1 - π(s);
  * dual_center_self: 对称中心 1/2 处反演对偶自闭合:
    1/(1/(1/2) + 1/(1/2)) = (1/2)·(1/2)。 -/

/-- 不动点 (实数轴): s = 1 - s ⟺ s = 1/2。 -/
theorem one_minus_fixed (s : ℝ) : s = 1 - s ↔ s = 1 / 2 := by
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    norm_num

/-- 不动点 (复平面): z = 1 - z ⟺ z = lift (1/2) — 对称中心在实轴上
的位置 1/2 (假复数轴上的投影位置)。 -/
theorem one_minus_fixed_cplx (z : ComplexAxis) : z = 1 - z ↔ z = lift (1 / 2) := by
  constructor
  · intro h
    ext
    · simp [lift]
      have ha : z.a = 1 - z.a := by
        simpa using congrArg ComplexAxis.a h
      nlinarith
    · simp [lift]
      have hb : z.b = -z.b := by
        simpa using congrArg ComplexAxis.b h
      nlinarith
  · intro h
    rw [h]
    ext <;> norm_num [lift]

/-- 函数方程映射的投影: π(1-s) = 1 - π(s) — s ↦ 1-s 在投影下是
实轴的反射 (不动点 1/2 = 反射中心)。 -/
theorem one_minus_proj (z : ComplexAxis) : proj (1 - z) = 1 - proj z := by
  simp [proj]

/-- 临界线条件: Re(s) = 1/2 ⟺ 1 - s = conj s — 临界线上 1-s 与 s
互为共轭 (函数方程 ξ(s)=ξ(1-s) 与实系数共轭对称的组合:
Re(s) = 1/2 时 ζ(s) 实值)。 -/
theorem critical_line_iff_conj (z : ComplexAxis) : proj z = 1 / 2 ↔ 1 - z = conj z := by
  constructor
  · intro h
    ext
    · change 1 - z.a = z.a
      have ha : z.a = 1 / 2 := by simpa [proj] using h
      rw [ha]
      norm_num
    · simp [conj]
  · intro h
    have ha : 1 - z.a = z.a := by
      simpa [conj] using congrArg ComplexAxis.a h
    change proj z = 1 / 2
    simp [proj]
    nlinarith

/-- 对称中心自对偶: 1/(1/(1/2) + 1/(1/2)) = (1/2)·(1/2) — 反演对偶
在中心 1/2 处自闭合 (调和对偶特例, C012 的临界条件版本)。 -/
theorem dual_center_self : recip (recip (lift (1 / 2)) + recip (lift (1 / 2))) = lift (1 / 2) * lift (1 / 2) := by
  rw [recip_lift (1 / 2) (by norm_num)]
  rw [← lift_add]
  norm_num
  rw [recip_lift 4 (by norm_num)]
  rw [← lift_mul]
  congr 1
  norm_num

/-! ## 反射的平方根: 1/2 的对称是复数开方的产物

以 1/2 为中心的反射 s ↦ 1-s (180° 对称) 是"开方"结构: 它存在变换平方根
φ(z) = i·z + (1-i)/2, 满足 φ∘φ = 反射。i = √(-1) (C011 的 J, 90° 旋转)
— 180° 对称的开方 = 90° 旋转 (i 打转的一半); 平方根变换的系数
(1-i)/2 = 1/(1+i) 又是反演对偶的分母 (2 = |1+i|²)。
(KNOWN: 仿射变换群中反射的平方根, 标准事实。) -/

-- φ(z) = i·z + (1-i)/2 的分量形式: iz = ⟨-z.b, z.a⟩, (1-i)/2 = ⟨1/2, -1/2⟩。
/-- 反射的平方根: φ(z) = i·z + (1-i)/2 — φ∘φ = (s ↦ 1-s) 关于 1/2 的反射。 -/
noncomputable def reflectSqrt (z : ComplexAxis) : ComplexAxis :=
  ⟨-z.b + 1 / 2, z.a - 1 / 2⟩

-- ψ(z) = -i·z + (1+i)/2 的分量形式: -iz = ⟨z.b, -z.a⟩, (1+i)/2 = ⟨1/2, 1/2⟩。
/-- 反射的另一个平方根: ψ(z) = -i·z + (1+i)/2 — ψ∘ψ 也是反射。 -/
noncomputable def reflectSqrt' (z : ComplexAxis) : ComplexAxis :=
  ⟨z.b + 1 / 2, -z.a + 1 / 2⟩

/-- φ∘φ = 反射: reflectSqrt (reflectSqrt z) = 1 - z —
以 1/2 为中心的 180° 对称是 90° 旋转 (i) 的平方。 -/
theorem reflectSqrt_sq (z : ComplexAxis) : reflectSqrt (reflectSqrt z) = 1 - z := by
  unfold reflectSqrt
  ext <;> simp <;> ring_nf

/-- ψ∘ψ = 反射: 另一个平方根同样给出 1 - z。 -/
theorem reflectSqrt'_sq (z : ComplexAxis) : reflectSqrt' (reflectSqrt' z) = 1 - z := by
  unfold reflectSqrt'
  ext <;> simp <;> ring_nf

/-! ## 素数可达定理: 两次基点漂移精确命中素数

沿平移轴数整数点 1,2,3,..., 整数点经两次基点漂移 (漂移 1: 基点 0→i,
n ↦ n + i; 漂移 2: 反演漂移, 球心 1 半径 r) 后一般变成分数点; 仍为整数
的位置由 (n-1)²+1 | r² 决定 (高斯范数整除条件)。关键构造
(OBSERVATION/KNOWN, 数据验证 C014_drift_int_points.py):
  对每个素数 p 和 p-1 的每个因子 m, 取漂移半径 r² = (m²+1)(p-1)/m,
  整数点 n = m+1 两次漂移后投影恰好落在素数 p:
    π(F_r(m+1)) = 1 + r²·m/(m²+1) = 1 + (p-1) = p
— "素数恰好落在平移整数位" (docs/关于黎曼猜想的思考.md) 的构造版本。 -/

/-- 两次基点漂移: F_r(n) = I_{1,r}(n + i) — 整数点先经基点漂移 0→i,
再经反演漂移 (球心 1, 半径 r)。 -/
noncomputable def doubleDrift (r : ℝ) (n : ℕ) : ComplexAxis :=
  circleInv (lift 1) r (lift n + J)

/-- 两次漂移的投影: π(F_r(n)) = 1 + r²(n-1)/((n-1)²+1) — 整数点在
漂移下的投影位置。 -/
theorem doubleDrift_proj (r : ℝ) (n : ℕ) :
    proj (doubleDrift r n) = 1 + r ^ 2 * ((n : ℝ) - 1) / (((n : ℝ) - 1) ^ 2 + 1) := by
  unfold doubleDrift circleInv
  have hconj : conj (lift n + J) = lift n - J := by
    ext <;> simp [conj, lift, J] <;> ring
  rw [hconj]
  let t : ℝ := (n : ℝ) - 1
  have ht : lift n - J - lift 1 = lift t - J := by
    ext <;> simp [lift, J, t] <;> ring
  rw [ht]
  have hrecip : recip (lift t - J) = ⟨t / (t ^ 2 + 1), 1 / (t ^ 2 + 1)⟩ := by
    ext <;> simp [recip, lift, J] <;> ring
  rw [hrecip]
  simp [proj, lift, mul, add]
  ring

/-- 素数可达定理: 对素数 p 和 p-1 的因子 m, 取漂移半径 r² = (m²+1)(p-1)/m,
整数点 n = m+1 经两次基点漂移后投影恰好落在素数 p 上 —
"素数恰好落在平移整数位"的构造版本。 -/
theorem prime_reachable_by_drift (p m : ℕ) (hp : Nat.Prime p) (hm : m ∣ p - 1) :
    let r2 : ℕ := ((m ^ 2 + 1) * (p - 1)) / m
    proj (doubleDrift (Real.sqrt r2) (m + 1)) = (p : ℝ) := by
  let r2 : ℕ := ((m ^ 2 + 1) * (p - 1)) / m
  change proj (doubleDrift (Real.sqrt r2) (m + 1)) = (p : ℝ)
  rw [doubleDrift_proj (Real.sqrt r2) (m + 1)]
  have hsq : (Real.sqrt (r2 : ℝ)) ^ 2 = (r2 : ℝ) := Real.sq_sqrt (by exact_mod_cast Nat.zero_le r2)
  rw [hsq]
  have ht : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by
    simp [Nat.cast_add]
  rw [ht]
  have hmul : m ∣ (m ^ 2 + 1) * (p - 1) := dvd_mul_of_dvd_right hm _
  have hr2 : r2 * m = (m ^ 2 + 1) * (p - 1) := Nat.div_mul_cancel hmul
  have hcast : (r2 : ℝ) * (m : ℝ) / ((m : ℝ) ^ 2 + 1) = ((p - 1 : ℕ) : ℝ) := by
    have hc : (r2 : ℝ) * (m : ℝ) = ((m ^ 2 + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hr2
    rw [hc]
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    field_simp
  rw [hcast]
  have hp1 : 1 ≤ p := (Nat.Prime.one_lt hp).le
  rw [Nat.cast_sub hp1]
  ring

/-! ## 素数按复数进制重构为两个轴

素数 (假复数轴上的整数位命中集) 按复数进制 (高斯整数 Z[i]) 重新构造:
  * norm z := z.a² + z.b² — 范数 (recip 的分母, 高斯整数范数 |a+bi|²);
  * Fermat 两平方和 (KNOWN, mathlib Nat.Prime.sq_add_sq): p ≢ 3 (mod 4)
    的素数 p 是某高斯整数的范数 — 存在两轴坐标 (a, b) 使 p = a² + b²,
    即素数在 ComplexAxis 中对应点 a + bJ (两轴);
  * p ≡ 3 (mod 4) 时 p 是高斯素数, 不可拆 (单轴);
  * 素数可达定理的半径配方里 (m²+1) = norm (lift m + J) — 漂移半径的
    高斯范数正是本节的范数 (两处同构)。 -/

/-- 范数: |z|² = z.a² + z.b² — 高斯整数的范数 (recip 的分母)。 -/
def norm (z : ComplexAxis) : ℝ := z.a ^ 2 + z.b ^ 2

/-- recip 的分母就是范数。 -/
theorem recip_denom_is_norm (z : ComplexAxis) : z.a ^ 2 + z.b ^ 2 = norm z := rfl

/-- 漂移半径配方里的高斯范数: norm (lift m + J) = m² + 1 —
素数可达定理的 (m²+1) 正是整数点 m+i 的范数。 -/
theorem norm_lift_add_J (m : ℕ) : norm (lift m + J) = (m : ℝ) ^ 2 + 1 := by
  simp [norm, lift, J]

/-- 素数按复数进制重构为两个轴 (Fermat 两平方和): p ≢ 3 (mod 4) 的素数
p 是 ComplexAxis 中某点的范数 — 存在两轴坐标 (a, b) 使 p = a² + b²
(高斯整数分解 p = |a+bi|²)。p ≡ 3 (mod 4) 时 p 是高斯素数, 不可拆。 -/
theorem prime_two_axis (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 ≠ 3) :
    ∃ z : ComplexAxis, norm z = (p : ℝ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.Prime.sq_add_sq (p := p) hmod with ⟨a, b, hab⟩
  refine ⟨⟨a, b⟩, ?_⟩
  simp [norm]
  exact_mod_cast hab

/-! ## 蜷曲性: 反演把无限远卷回有限

复数轴 (无论真假) 是蜷曲的 ⟹ 无限与有限无差别 (紧致性)。精确陈述
(OBSERVATION/KNOWN): 反演把远离的点卷回球心 —
  * norm_recip: norm (recip z) = 1/norm z — |z| 越大 |recip z| 越小,
    无限远 → 0;
  * recip_vanishes_at_infinity: 对任意 ε, 存在 R, norm z > R ⟹
    norm (recip z) < ε;
  * circleInv_vanishes_at_infinity: 远离的点被卷回球心 c 的 ε 邻域
    (r = 1 版本)。
这解释了 ζ 解析延拓的本质: 平坦轴上 1+2+3+... 发散 (无限≠有限);
蜷曲后 ζ(-1) = -1/12 (无限=有限) — 级数的"发散"在蜷曲结构里是有限对象。 -/

/-- 共轭保持范数: norm (conj z) = norm z。 -/
theorem norm_conj (z : ComplexAxis) : norm (conj z) = norm z := by
  simp [norm, conj]

/-- 反演的范数: norm (recip z) = 1 / norm z — 反演把远离的点卷回原点附近。 -/
theorem norm_recip (z : ComplexAxis) : norm (recip z) = 1 / norm z := by
  cases z with
  | mk a b =>
    by_cases hsq : a ^ 2 + b ^ 2 ≠ 0
    · simp [norm, recip]
      field_simp [hsq]
    · have hs : a ^ 2 + b ^ 2 = 0 := not_not.mp hsq
      have ha : a = 0 := by
        have : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, hs]
        exact sq_eq_zero_iff.mp this
      have hb : b = 0 := by
        have : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, hs]
        exact sq_eq_zero_iff.mp this
      simp [norm, recip, ha, hb]

/-- 反演把无限远卷回 0: 对任意 ε > 0, 存在 R, norm z > R ⟹ norm (recip z) < ε。 -/
theorem recip_vanishes_at_infinity (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ComplexAxis, norm z > R → norm (recip z) < ε := by
  refine ⟨1 / ε, ?_⟩
  intro z hz
  rw [norm_recip]
  have hnz : 0 < norm z := lt_trans (by positivity : 0 < 1 / ε) hz
  have h1 : 1 < ε * norm z := by
    calc
      1 = ε * (1 / ε) := by field_simp [hε.ne']
      _ < ε * norm z := mul_lt_mul_of_pos_left hz hε
  exact (div_lt_iff₀ hnz).2 h1

/-- 反演漂移把无限远卷回球心 (球心在实轴): 对任意 ε > 0, 存在 R,
|z - c| > R ⟹ circleInv c 1 z 落在球心 c 的 ε 邻域内。 -/
theorem circleInv_vanishes_at_infinity (c : ComplexAxis) (hc : c.b = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ComplexAxis, norm (z - c) > R → norm (circleInv c 1 z - c) < ε := by
  refine ⟨1 / ε, ?_⟩
  intro z hz
  unfold circleInv
  have hx : (c + lift (1 ^ 2) * recip (conj z - c)) - c = recip (conj z - c) := by
    ext <;> simp [lift] <;> ring
  rw [hx]
  rw [norm_recip]
  have hnorm : norm (conj z - c) = norm (z - c) := by
    simp [norm, conj, hc]
  rw [hnorm]
  have hnz : 0 < norm (z - c) := lt_trans (by positivity : 0 < 1 / ε) hz
  have h1 : 1 < ε * norm (z - c) := by
    calc
      1 = ε * (1 / ε) := by field_simp [hε.ne']
      _ < ε * norm (z - c) := mul_lt_mul_of_pos_left hz hε
  exact (div_lt_iff₀ hnz).2 h1

/-! ## 圆上整点与 90° 循环: 素数分裂的几何

素数 p ≡ 1 (mod 4) ⟺ 圆 x²+y² = p 上有整点 (Fermat 两平方和, C014)。
圆上整点的几何结构 (OBSERVATION/KNOWN):
  * rot90 z := ⟨-z.b, z.a⟩ — 90° 旋转 (乘 J);
  * 旋转保持范数: 圆上的点仍在圆上 (norm (rot90 z) = norm z);
  * 旋转 4 循环: rot90⁴ = id — 周期性穿越; R² = -z (半圈反转);
  * 旋转保持格点: 整数格点旋转后仍是整数格点;
  * 8 个符号/顺序变体在同一圆上 (符号变体 norm_neg_b, 顺序变体
    norm_swap, 旋转变体 rot90_norm);
  * p ≡ 3 (mod 4): 圆上无整点 (两平方和永不 ≡ 3 mod 4) — 素数不分裂,
    这正是"模 4 判别"的几何版: 圆上有无整点。 -/

/-- 90° 旋转: R(z) = ⟨-z.b, z.a⟩ (即乘 J)。 -/
def rot90 (z : ComplexAxis) : ComplexAxis := ⟨-z.b, z.a⟩

/-- 旋转保持范数: norm (R z) = norm z — 圆上的点仍在圆上。 -/
theorem rot90_norm (z : ComplexAxis) : norm (rot90 z) = norm z := by
  simp [rot90, norm]
  ring

/-- 旋转两次 = 关于原点的反转: R²(z) = -z (半圈)。 -/
theorem rot90_sq (z : ComplexAxis) : rot90 (rot90 z) = -z := by
  change rot90 (rot90 z) = neg z
  ext <;> simp [rot90, neg] <;> ring

/-- 旋转 4 次回到自身: R⁴ = id — 90° 循环的周期性 (穿越圆上整点)。 -/
theorem rot90_four (z : ComplexAxis) : rot90 (rot90 (rot90 (rot90 z))) = z := by
  ext <;> simp [rot90] <;> ring

/-- 旋转与 J 乘法一致: rot90 z = J * z (旋转即乘虚单位)。 -/
theorem rot90_eq_J_mul (z : ComplexAxis) : rot90 z = J * z := by
  ext <;> simp [rot90, J, mul] <;> ring

/-- 旋转保持格点: 整数格点旋转后仍是整数格点 — 90° 循环在格点之间跳跃。 -/
theorem rot90_keeps_lattice (a b : ℤ) :
    rot90 (⟨(a : ℝ), (b : ℝ)⟩ : ComplexAxis) = ⟨-(b : ℝ), (a : ℝ)⟩ := by
  simp [rot90]

/-- 符号变体在同一圆上: norm ⟨a, -b⟩ = norm ⟨a, b⟩。 -/
theorem norm_neg_b (a b : ℝ) : norm ⟨a, -b⟩ = norm ⟨a, b⟩ := by
  simp [norm]

/-- 顺序变体在同一圆上: norm ⟨b, a⟩ = norm ⟨a, b⟩。 -/
theorem norm_swap (a b : ℝ) : norm ⟨b, a⟩ = norm ⟨a, b⟩ := by
  simp [norm]
  ring

/-- 平方模 4: 平方数模 4 只可能是 0 或 1。 -/
theorem sq_mod_four (x : ℕ) : (x ^ 2) % 4 = 0 ∨ (x ^ 2) % 4 = 1 := by
  have hlt : x % 4 < 4 := Nat.mod_lt x (by norm_num : 0 < 4)
  interval_cases hx : x % 4
  · left
    norm_num [Nat.pow_mod, hx]
  · right
    norm_num [Nat.pow_mod, hx]
  · left
    norm_num [Nat.pow_mod, hx]
  · right
    norm_num [Nat.pow_mod, hx]

/-- 两平方和永不 ≡ 3 (mod 4): 圆 x²+y² 的半径平方碰不到 3 mod 4。 -/
theorem sq_add_sq_not_three_mod_four (a b : ℕ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  rcases sq_mod_four a with ha0 | ha1 <;> rcases sq_mod_four b with hb0 | hb1
  · rw [Nat.add_mod, ha0, hb0]
    norm_num
  · rw [Nat.add_mod, ha0, hb1]
    norm_num
  · rw [Nat.add_mod, ha1, hb0]
    norm_num
  · rw [Nat.add_mod, ha1, hb1]
    norm_num

/-- p ≡ 3 (mod 4) 的素数不是两平方和: 圆 x²+y² = p 上没有整点 —
素数不分裂 (圆空 ⟺ 高斯素数)。 -/
theorem prime_not_sq_add_sq_three_mod_four (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 3) :
    ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  rintro ⟨a, b, hab⟩
  have : (a ^ 2 + b ^ 2) % 4 = 3 := by
    rw [hab]
    exact hmod
  exact sq_add_sq_not_three_mod_four a b this

/-! ## 拓宽到整个圆: 圆上整点的完整结构

不局限于素数, 对任意半径的圆 x²+y² = n, 抓圆上所有整点
(OBSERVATION/KNOWN):
  * isLattice: 整点 (两轴坐标都是整数);
  * norm_mul: 范数乘性 norm (z·w) = norm z · norm w — 圆与圆的乘法链接
    (合数 65 = 5·13 的 16 个整点 = 5 和 13 的分解组合; 圆上整点数由
    半径的素数分解决定);
  * lattice_mul: 整点乘法封闭 — 圆上整点构成环 (高斯整数 Z[i]);
  * orbit_closed: 旋转 4 循环 × 共轭镜像 (最多 8 点) 全在同一圆上 —
    圆上整点的轨道结构。 -/

/-- 整点: 复数轴格点 (两轴坐标 a, b 都是整数)。 -/
def isLattice (z : ComplexAxis) : Prop := ∃ a b : ℤ, z = ⟨(a : ℝ), (b : ℝ)⟩

/-- 范数乘性: norm (z·w) = norm z · norm w — 圆的乘法链接 (圆 n 与圆 m
的整点乘出圆 nm 的整点)。 -/
theorem norm_mul (z w : ComplexAxis) : norm (z * w) = norm z * norm w := by
  simp [norm, mul]
  ring

/-- 整点乘法封闭: 整点乘积仍是整点 — 圆上整点构成环 (高斯整数 Z[i])。 -/
theorem lattice_mul (z w : ComplexAxis) (hz : isLattice z) (hw : isLattice w) :
    isLattice (z * w) := by
  rcases hz with ⟨a, b, rfl⟩
  rcases hw with ⟨c, d, rfl⟩
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  ext
  · simp [mul, Int.cast_mul, Int.cast_sub]
  · simp [mul, Int.cast_mul, Int.cast_add]

/-- 轨道封闭: 旋转 (4 循环) 与共轭 (镜像) 保持整点且保持范数 —
从任一圆上整点出发, 旋转×镜像轨道 (最多 8 点) 全在同一圆上。 -/
theorem orbit_closed (z : ComplexAxis) :
    norm z = norm (rot90 z) ∧ norm z = norm (conj z) ∧
      norm z = norm (rot90 (conj z)) := by
  constructor
  · exact (rot90_norm z).symm
  · constructor
    · exact (norm_conj z).symm
    · rw [rot90_norm, norm_conj]

/-! ## 素数圆上单轨道: 两平方和分解唯一 (UFD)

素数 p ≡ 1 (mod 4) 的圆 x²+y² = p 上恰好只有一条轨道 (8 个符号×顺序
变体) — 两平方和表示唯一 (不计符号与顺序)。证明用高斯整数 Z[i] 的
唯一分解 (EuclideanDomain ⟹ UFD, mathlib):
  * norm α = p 素数 ⟹ α 不可约;
  * norm β = p ⟹ β 不可约; β·star β = p = α·star α ⟹ β | α·star α;
  * UFD 中 prime 的 Euclid 引理: β | α 或 β | star α;
  * 相伴 ⟹ β = α·u 或 β = star α·u, u 单位 = {±1, ±i} (norm 1);
  * 展开 ⟹ (c,d) 是 (a,b) 的符号/顺序变体 — 圆上只有锁定的那条轨道。
(KNOWN: 两平方和表示唯一, 经典数论。) -/

/-- 高斯整数中范数为 1 的元素 = 单位 {±1, ±i}。 -/
private lemma gauss_unit_of_norm_one (x : GaussianInt) (hx : x.norm = 1) :
    x = 1 ∨ x = -1 ∨ x = ⟨0, 1⟩ ∨ x = ⟨0, -1⟩ := by
  cases x with
  | mk re im =>
    have hri : (re : ℤ) ^ 2 + (im : ℤ) ^ 2 = 1 := by
      simpa [Zsqrtd.norm, pow_two, sub_eq_add_neg] using hx
    have hriR : (re : ℝ) ^ 2 + (im : ℝ) ^ 2 = 1 := by exact_mod_cast hri
    have hre2 : (re : ℝ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (im : ℝ), hriR]
    have hre : -1 ≤ re ∧ re ≤ 1 := by
      have hlo : -1 ≤ (re : ℝ) := by nlinarith [sq_nonneg ((re : ℝ) + 1), hre2]
      have hhi : (re : ℝ) ≤ 1 := by nlinarith [sq_nonneg ((re : ℝ) - 1), hre2]
      constructor
      · exact_mod_cast hlo
      · exact_mod_cast hhi
    have hre_cases : re = -1 ∨ re = 0 ∨ re = 1 := by omega
    rcases hre_cases with rfl | rfl | rfl
    · have him2 : (im : ℝ) ^ 2 = 0 := by
        have : (1 : ℝ) + (im : ℝ) ^ 2 = 1 := by simpa using hriR
        nlinarith
      have him : im = 0 := by exact_mod_cast (sq_eq_zero_iff.mp him2)
      right; left
      ext <;> simp [him]
    · have him1 : im = 1 ∨ im = -1 := by
        have : (im : ℝ) ^ 2 = 1 := by simpa using hriR
        have : (im : ℝ) = 1 ∨ (im : ℝ) = -1 := sq_eq_one_iff.mp this
        rcases this with h1 | h2
        · left
          exact_mod_cast h1
        · right
          exact_mod_cast h2
      rcases him1 with him | him
      · right; right; left
        ext <;> simp [him]
      · right; right; right
        ext <;> simp [him]
    · have him2 : (im : ℝ) ^ 2 = 0 := by
        have : (1 : ℝ) + (im : ℝ) ^ 2 = 1 := by simpa using hriR
        nlinarith
      have him : im = 0 := by exact_mod_cast (sq_eq_zero_iff.mp him2)
      left
      ext <;> simp [him]

/-- 高斯整数中范数为素数 p 的元素不可约。 -/
private lemma gauss_irreducible_of_norm_prime {p : ℕ} (hp : Nat.Prime p)
    {x : GaussianInt} (hx : x.norm = (p : ℤ)) : Irreducible x := by
  constructor
  · intro hu
    have hn : x.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) x).2 hu
    have h1 : (1 : ℤ) = (p : ℤ) := hn.symm.trans hx
    exact (Nat.Prime.ne_one hp) (by exact_mod_cast h1.symm)
  · intro y z hyz
    by_cases hyu : IsUnit y
    · exact Or.inl hyu
    · by_cases hzu : IsUnit z
      · exact Or.inr hzu
      · exfalso
        have hx0 : x ≠ 0 := by
          intro h0
          have : x.norm = 0 := by rw [h0]; simp
          have : (p : ℤ) = 0 := hx.symm.trans this
          have : p = 0 := by exact_mod_cast this
          exact (Nat.Prime.ne_zero hp) this
        have hy0 : y ≠ 0 := by
          intro h0
          apply hx0
          rw [hyz, h0]
          simp
        have hz0 : z ≠ 0 := by
          intro h0
          apply hx0
          rw [hyz, h0]
          simp
        have hny1 : (1 : ℤ) ≤ y.norm := by
          have : 0 < y.norm := GaussianInt.norm_pos.2 hy0
          omega
        have hnz1 : (1 : ℤ) ≤ z.norm := by
          have : 0 < z.norm := GaussianInt.norm_pos.2 hz0
          omega
        have hnyne1 : y.norm ≠ 1 := by
          intro h1
          apply hyu
          exact (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) y).1 h1
        have hny2 : (2 : ℤ) ≤ y.norm := by omega
        have hnzne1 : z.norm ≠ 1 := by
          intro h1
          apply hzu
          exact (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) z).1 h1
        have hnz2 : (2 : ℤ) ≤ z.norm := by omega
        have hn : (p : ℤ) = y.norm * z.norm := by
          rw [← hx]
          rw [hyz]
          exact Zsqrtd.norm_mul y z
        have hdiv : y.norm ∣ (p : ℤ) := ⟨z.norm, hn⟩
        have hdivN : y.norm.natAbs ∣ p := by
          exact (Int.natAbs_dvd_natAbs).2 hdiv
        have hnyabs : y.norm.natAbs = y.norm := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg y)
        have hynorm : y.norm = 1 ∨ y.norm = (p : ℤ) := by
          rcases (Nat.Prime.eq_one_or_self_of_dvd hp y.norm.natAbs hdivN) with h1 | hp'
          · left
            have hc : (y.norm.natAbs : ℤ) = 1 := by exact_mod_cast h1
            rwa [hnyabs] at hc
          · right
            have hc : (y.norm.natAbs : ℤ) = (p : ℤ) := by exact_mod_cast hp'
            rwa [hnyabs] at hc
        have hynp : y.norm = (p : ℤ) := hynorm.resolve_left hnyne1
        have hzn : z.norm = 1 := by
          have hz : (p : ℤ) = (p : ℤ) * z.norm := by
            rwa [hynp] at hn
          have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
          exact (mul_left_cancel₀ hp0 (by simpa using hz.symm))
        exact hzu ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) z).1 hzn)

/-- 素数两平方和分解唯一 (不计符号与顺序): 若 p 素数且 p = a²+b² = c²+d²,
则 (c,d) 是 (a,b) 的符号/顺序变体 — 圆 x²+y² = p 上只有锁定的那条轨道。 -/
theorem prime_sq_add_sq_unique (p : ℕ) (a b c d : ℤ) (hp : Nat.Prime p)
    (h1 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ)) (h2 : (c : ℤ) ^ 2 + (d : ℤ) ^ 2 = (p : ℤ)) :
    (|c| = |a| ∧ |d| = |b|) ∨ (|c| = |b| ∧ |d| = |a|) := by
  let α : GaussianInt := ⟨a, b⟩
  let β : GaussianInt := ⟨c, d⟩
  have hα : α.norm = (p : ℤ) := by
    simp [α, Zsqrtd.norm]
    rw [← pow_two, ← pow_two]
    exact h1
  have hβ : β.norm = (p : ℤ) := by
    simp [β, Zsqrtd.norm]
    rw [← pow_two, ← pow_two]
    exact h2
  have hirrα : Irreducible α := gauss_irreducible_of_norm_prime hp hα
  have hirrβ : Irreducible β := gauss_irreducible_of_norm_prime hp hβ
  have hprod : β * star β = α * star α := by
    have hb : β * star β = ⟨(p : ℤ), 0⟩ := by
      ext
      · rw [Zsqrtd.re_mul]
        simp [β]
        rw [← pow_two, ← pow_two]
        exact h2
      · rw [Zsqrtd.im_mul]
        simp [β]
        ring
    have ha : α * star α = ⟨(p : ℤ), 0⟩ := by
      ext
      · rw [Zsqrtd.re_mul]
        simp [α]
        rw [← pow_two, ← pow_two]
        exact h1
      · rw [Zsqrtd.im_mul]
        simp [α]
        ring
    exact hb.trans ha.symm
  have hbdvd : β ∣ α * star α := by
    refine ⟨star β, ?_⟩
    rw [← hprod]
  have hprime : Prime β :=
    (UniqueFactorizationMonoid.irreducible_iff_prime (α := GaussianInt)).1 hirrβ
  rcases hprime.dvd_or_dvd hbdvd with hbα | hbs
  · rcases hbα with ⟨γ, hγ⟩
    have hnormγ : γ.norm = 1 := by
      have hn : (p : ℤ) = (p : ℤ) * γ.norm := by
        calc
          (p : ℤ) = Zsqrtd.norm α := hα.symm
          _ = Zsqrtd.norm (β * γ) := by rw [hγ]
          _ = Zsqrtd.norm β * Zsqrtd.norm γ := Zsqrtd.norm_mul β γ
          _ = (p : ℤ) * γ.norm := by rw [hβ]
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
      exact (mul_left_cancel₀ hp0 (by simpa using hn.symm))
    rcases gauss_unit_of_norm_one γ hnormγ with rfl | rfl | rfl | rfl
    · have hαβ : (⟨a, b⟩ : GaussianInt) = ⟨c, d⟩ := by simpa [α, β] using hγ
      have hc : c = a := by
        have : a = c := by simpa using congrArg Zsqrtd.re hαβ
        exact this.symm
      have hd : d = b := by
        have : b = d := by simpa using congrArg Zsqrtd.im hαβ
        exact this.symm
      left
      constructor <;> simp [hc, hd]
    · have hαβ : (⟨a, b⟩ : GaussianInt) = -⟨c, d⟩ := by simpa [α, β] using hγ
      have hc : c = -a := by
        have : a = -c := by simpa using congrArg Zsqrtd.re hαβ
        omega
      have hd : d = -b := by
        have : b = -d := by simpa using congrArg Zsqrtd.im hαβ
        omega
      left
      constructor <;> simp [hc, hd]
    · have hαβ : (⟨a, b⟩ : GaussianInt) = ⟨c, d⟩ * ⟨0, 1⟩ := by simpa [α, β] using hγ
      have hc : c = b := by
        have : b = c := by simpa using congrArg Zsqrtd.im hαβ
        exact this.symm
      have hd : d = -a := by
        have : a = -d := by simpa using congrArg Zsqrtd.re hαβ
        omega
      right
      constructor <;> simp [hc, hd]
    · have hαβ : (⟨a, b⟩ : GaussianInt) = ⟨c, d⟩ * ⟨0, -1⟩ := by simpa [α, β] using hγ
      have hc : c = -b := by
        have : b = -c := by simpa using congrArg Zsqrtd.im hαβ
        omega
      have hd : d = a := by
        have : a = d := by simpa using congrArg Zsqrtd.re hαβ
        exact this.symm
      right
      constructor <;> simp [hc, hd]
  · rcases hbs with ⟨γ, hγ⟩
    have hnormγ : γ.norm = 1 := by
      have hn : (p : ℤ) = (p : ℤ) * γ.norm := by
        calc
          (p : ℤ) = Zsqrtd.norm α := hα.symm
          _ = Zsqrtd.norm (star α) := by
            simp [α, Zsqrtd.norm]
          _ = Zsqrtd.norm (β * γ) := by rw [hγ]
          _ = Zsqrtd.norm β * Zsqrtd.norm γ := Zsqrtd.norm_mul β γ
          _ = (p : ℤ) * γ.norm := by rw [hβ]
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
      exact (mul_left_cancel₀ hp0 (by simpa using hn.symm))
    rcases gauss_unit_of_norm_one γ hnormγ with rfl | rfl | rfl | rfl
    · have hαβ : star (⟨a, b⟩ : GaussianInt) = ⟨c, d⟩ := by simpa [α, β] using hγ
      have hc : c = a := by
        have : a = c := by simpa using congrArg Zsqrtd.re hαβ
        exact this.symm
      have hd : d = -b := by
        have : -b = d := by simpa using congrArg Zsqrtd.im hαβ
        exact this.symm
      left
      constructor <;> simp [hc, hd]
    · have hαβ : star (⟨a, b⟩ : GaussianInt) = -⟨c, d⟩ := by simpa [α, β] using hγ
      have hc : c = -a := by
        have : a = -c := by simpa using congrArg Zsqrtd.re hαβ
        omega
      have hd : d = b := by
        have : -b = -d := by simpa using congrArg Zsqrtd.im hαβ
        omega
      left
      constructor <;> simp [hc, hd]
    · have hαβ : star (⟨a, b⟩ : GaussianInt) = ⟨c, d⟩ * ⟨0, 1⟩ := by simpa [α, β] using hγ
      have hc : c = -b := by
        have : -b = c := by simpa using congrArg Zsqrtd.im hαβ
        exact this.symm
      have hd : d = -a := by
        have : a = -d := by simpa using congrArg Zsqrtd.re hαβ
        omega
      right
      constructor <;> simp [hc, hd]
    · have hαβ : star (⟨a, b⟩ : GaussianInt) = ⟨c, d⟩ * ⟨0, -1⟩ := by simpa [α, β] using hγ
      have hc : c = b := by
        have : -b = -c := by simpa using congrArg Zsqrtd.im hαβ
        omega
      have hd : d = a := by
        have : a = d := by simpa using congrArg Zsqrtd.re hαβ
        exact this.symm
      right
      constructor <;> simp [hc, hd]


/-! ## 临界线是圆: 1/2 竖线在蜷曲下 = 圆心 (1,0) 的圆

回到实数 0 点视角: 临界线 (竖直线 x = 1/2, {1/2 + t·J}) 在反演
(蜷曲, C015) 下是圆: w = recip z ⟹ |w - 1| = 1 — 圆心 (1,0) 半径 1,
正是"以 (1,0) 为球心的球面"。圆经过 0 (z = ∞, 无限远被蜷曲卷回原点)
和 2 (z = 1/2)。竖直线两端 (±∞) 蜷曲为同一点 ⟹ 直线闭合为圆。
(OBSERVATION/KNOWN: 圆反演把直线映成圆, 经典。) -/

/-- 临界线在反演 (蜷曲) 下是圆: z = 1/2 + t·J ⟹ recip z 在圆心 (1,0)
半径 1 的圆上: norm (recip z - lift 1) = 1。 -/
theorem critical_line_is_circle (t : ℝ) :
    norm (recip (lift (1 / 2) + lift t * J) - lift 1) = 1 := by
  have hz : lift (1 / 2) + lift t * J = ⟨1 / 2, t⟩ := by
    ext <;> simp [J, lift, mul] <;> ring
  rw [hz]
  simp [norm, recip, lift]
  field_simp
  · nlinarith [sq_nonneg t]


/-! ## 零点位置的轴参数化: 黎曼函数在瞎tm平移反演轴视角下的形状

ζ 的零点 (黎曼猜想对象) 在两根轴上的位置 (OBSERVATION/KNOWN, 纯代数
位置参数化, 不涉及 ζ 的分析值):
  * 临界线 (非平凡零点, 猜想): 假复数轴 = 1/2, 真复数轴自由 —
    临界线 = 过假复数轴 1/2 位置、沿真复数轴 J 方向的直线
    {lift(1/2) + t·J : t ∈ ℝ} (critical_line_points);
  * 平凡零点: 真复数轴 = 0, 假复数轴 = 负偶整数 — 全在假复数轴上
    (real_axis_points: z.b = 0 ⟺ z 在抬升轴上);
  * 对偶: 临界线 (J 方向) 与瞎tm平移反演轴 (实方向 axisLine) 垂直。 -/

/-- 临界线上的点: proj z = 1/2 ⟺ z = 假复数轴位置 1/2 + 真复数轴
任意位置 t·J — 非平凡零点 (猜想) 的坐标形式: 假复数轴固定 1/2,
真复数轴自由。 -/
theorem critical_line_points (z : ComplexAxis) :
    proj z = 1 / 2 ↔ ∃ t : ℝ, z = lift (1 / 2) + lift t * J := by
  constructor
  · intro h
    refine ⟨z.b, ?_⟩
    ext
    · simp [J, lift, mul]
      simpa [proj] using h
    · simp [J, lift, mul]
  · rintro ⟨t, rfl⟩
    simp [proj, J, lift, mul]

/-- 平凡零点的位置形式: 真复数轴 = 0 ⟹ 点全在假复数轴 (抬升轴) 上:
z.b = 0 ⟺ ∃ r : ℝ, z = lift r。 -/
theorem real_axis_points (z : ComplexAxis) : z.b = 0 ↔ ∃ r : ℝ, z = lift r := by
  constructor
  · intro h
    refine ⟨z.a, ?_⟩
    ext <;> simp [lift, h]
  · rintro ⟨r, rfl⟩
    simp [lift]

/-- 非平凡零点 (猜想) 的位置: 假复数轴 = 1/2 且真复数轴非零 —
临界线上剔除平凡 (实轴) 点。 -/
theorem nontrivial_zero_position (z : ComplexAxis) :
    proj z = 1 / 2 ∧ z.b ≠ 0 ↔
      ∃ t : ℝ, t ≠ 0 ∧ z = lift (1 / 2) + lift t * J := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases (critical_line_points z).1 h1 with ⟨t, ht⟩
    refine ⟨t, ?_, ht⟩
    intro ht0
    apply h2
    rw [ht, ht0]
    simp [lift, J, mul]
  · rintro ⟨t, ht0, rfl⟩
    constructor
    · simp [proj, J, lift, mul]
    · intro hb
      apply ht0
      have : (lift (1 / 2) + lift t * J).b = t := by simp [J, lift, mul]
      exact this.symm.trans hb
/-! ## 两个圆: 素数圆与临界线圆

素数圆 (圆心真 0 点, 半径 √p): 素数 p = a²+b² 的整点所在 (C014/C015)。
临界线圆 (圆心 (1,0), 半径 1): 临界线 (1/2 竖线) 在蜷曲 (反演) 下的像
(C019), 经过 0 (∞ 卷回) 和 2。
用户洞察: 假复数轴是 i 的后继 (打转) — 蜷曲视角下"圆"不止一个:
素数圆围绕真 0 点, 临界线圆经过真 0 点; 假复数轴 (实轴) 自身在黎曼
球面上也是圆 (经过 0 和 ∞ 的大圆)。反演关系: 临界线 → 临界线圆;
素数圆 → 同心圆 (半径 1/√p)。
(OBSERVATION/KNOWN。) -/

/-- 素数圆: 圆心真 0 点半径 √p (素数 p 的两平方和整点所在)。 -/
def primeCircle (p : ℕ) : Set ComplexAxis := {z : ComplexAxis | norm z = (p : ℝ)}

/-- 临界线圆: 圆心 (1,0) 半径 1 (临界线在蜷曲下的像, 经过 0 和 2)。 -/
def criticalCircle : Set ComplexAxis := {w : ComplexAxis | norm (w - lift 1) = 1}

/-- 临界线圆经过真 0 点: 0 ∈ criticalCircle (∞ 被蜷曲卷回的位置)。 -/
theorem zero_in_criticalCircle : (0 : ComplexAxis) ∈ criticalCircle := by
  simp [criticalCircle, norm, lift]

/-- 素数圆在反演下是同心圆: recip 把半径 √p 的圆 (圆心 0) 映到半径
1/√p 的圆 (norm_recip: norm (recip z) = 1/norm z)。 -/
theorem primeCircle_recip (p : ℕ) (z : ComplexAxis) (hz : norm z = (p : ℝ)) :
    norm (recip z) = 1 / (p : ℝ) := by
  rw [norm_recip, hz]

/-- 临界线在反演下映入临界线圆 (集合版): z 在临界线上 ⟹ recip z ∈ criticalCircle。 -/
theorem critical_line_in_circle (z : ComplexAxis) (hz : proj z = 1 / 2) :
    recip z ∈ criticalCircle := by
  rcases (critical_line_points z).1 hz with ⟨t, ht⟩
  rw [ht]
  exact critical_line_is_circle t





/-! ## 圆的交叉位置

三个圆 (实轴大圆、素数圆、临界线圆) 的交叉 (OBSERVATION/KNOWN):
  * 实轴 ∩ 临界线圆 = {0, 2}: 0 是 ∞ 卷回点, 2 是 1/2 的反演像;
  * 素数圆 ∩ 临界线圆: 圆心距 1, 相交当且仅当 p ≤ 4 (素数 p = 2, 3);
    交点满足 Re(z) = p/2; p = 2 时交点 = 1 ± i — 素数 2 的高斯分解点
    恰好是两个圆的交点;
  * p > 4: 素数圆与临界线圆不相交 (√p > 2)。 -/

/-- 实轴与临界线圆的交点: lift r ∈ criticalCircle ⟺ r = 0 ∨ r = 2。 -/
theorem realAxis_inter_criticalCircle (r : ℝ) :
    lift r ∈ criticalCircle ↔ r = 0 ∨ r = 2 := by
  constructor
  · intro h
    have h' : (r - 1) ^ 2 = 1 := by simpa [criticalCircle, norm, lift] using h
    have : (r - 1) = 1 ∨ (r - 1) = -1 := sq_eq_one_iff.mp h'
    rcases this with h1 | h2
    · right
      linarith
    · left
      linarith
  · rintro (h0 | h2)
    · rw [h0]
      simp [criticalCircle, norm, lift]
    · rw [h2]
      simp [criticalCircle, norm, lift]
      norm_num

/-- 素数圆与临界线圆的交点 (一般 p): z ∈ 两圆 ⟹ Re(z) = p/2
(由 |z-1|² = |z|² - 2Re(z) + 1 = 1 且 |z|² = p 推出)。 -/
theorem inter_proj (p : ℕ) (z : ComplexAxis) (h1 : z ∈ primeCircle p)
    (h2 : z ∈ criticalCircle) : proj z = (p : ℝ) / 2 := by
  have hnz : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [primeCircle, norm] using h1
  have hnw : (z.a - 1) ^ 2 + z.b ^ 2 = 1 := by simpa [criticalCircle, norm, lift] using h2
  change proj z = (p : ℝ) / 2
  simp [proj]
  nlinarith

/-- 素数 2 的圆与临界线圆的交点 = 高斯分解点: z ∈ primeCircle 2 ∧
z ∈ criticalCircle ⟺ z = ⟨1, 1⟩ ∨ z = ⟨1, -1⟩ (1 ± i, 2 = |1+i|²)。 -/
theorem prime2Circle_inter_criticalCircle (z : ComplexAxis) :
    z ∈ primeCircle 2 ∧ z ∈ criticalCircle ↔ z = ⟨1, 1⟩ ∨ z = ⟨1, -1⟩ := by
  constructor
  · rintro ⟨h1, h2⟩
    have hnz : z.a ^ 2 + z.b ^ 2 = 2 := by simpa [primeCircle, norm] using h1
    have hnw : (z.a - 1) ^ 2 + z.b ^ 2 = 1 := by simpa [criticalCircle, norm, lift] using h2
    have ha : z.a = 1 := by nlinarith
    have hb2 : z.b ^ 2 = 1 := by nlinarith [ha, hnz]
    have hb : z.b = 1 ∨ z.b = -1 := sq_eq_one_iff.mp hb2
    rcases hb with hb1 | hb2'
    · left
      ext <;> simp [ha, hb1]
    · right
      ext <;> simp [ha, hb2']
  · rintro (rfl | rfl)
    · simp [primeCircle, criticalCircle, norm, lift]
      norm_num
    · simp [primeCircle, criticalCircle, norm, lift]
      norm_num


/-! ## 假复数轴 1/2 位置的圆: 与临界线圆的对偶

圆心在假复数轴 1/2、半径 1/2 的圆 (经过真 0 点) 在反演下 = 竖直线 x = 1:
  * 竖直线 x = 1/2 (临界线) ⇄ 圆心 (1,0) 半径 1 的圆 (临界线圆);
  * 竖直线 x = 1 ⇄ 圆心 (1/2,0) 半径 1/2 的圆;
  * 两个圆 (圆心 1/2 与圆心 1) 在真 0 点内切 (|1 - 1/2| + 1/2 = 1) —
    平行线反演成内切圆, 切点 = 0 (∞ 卷回点)。
(OBSERVATION/KNOWN: 圆反演把平行直线映成内切圆。) -/

/-- 假复数轴 1/2 位置的圆 (圆心 (1/2,0) 半径 1/2, 经过真 0 点) 在
反演下 = 竖直线 x = 1: norm (z - lift(1/2)) = (1/2)² ⟺ proj (recip z) = 1。
(z ≠ 0: 0 在圆上但 recip 0 = 0, 0 是 ∞ 的代数对应。) -/
theorem halfCircle_recip (z : ComplexAxis) (hz : z ≠ 0) :
    norm (z - lift (1 / 2)) = (1 / 2 : ℝ) ^ 2 ↔ proj (recip z) = 1 := by
  constructor
  · intro h
    have h' : (z.a - 1 / 2) ^ 2 + z.b ^ 2 = (1 / 2 : ℝ) ^ 2 := by
      simpa [norm, lift] using h
    have hz2 : z.a ^ 2 + z.b ^ 2 = z.a := by
      nlinarith
    have ha0 : z.a ≠ 0 := by
      intro ha
      apply hz
      have : z.a ^ 2 + z.b ^ 2 = 0 := by
        rw [ha] at hz2
        nlinarith [sq_nonneg z.b, hz2]
      ext
      · exact ha
      · have : z.b ^ 2 = 0 := by nlinarith [sq_nonneg z.a, sq_nonneg z.b, this]
        exact sq_eq_zero_iff.mp this
    change proj (recip z) = 1
    simp [proj, recip]
    rw [hz2]
    field_simp [ha0]
  · intro h
    have hz2 : z.a ^ 2 + z.b ^ 2 = z.a := by
      -- proj (recip z) = 1: z.a/(z.a²+z.b²) = 1: 
      have h' : z.a / (z.a ^ 2 + z.b ^ 2) = 1 := by simpa [proj, recip] using h
      have hd : z.a ^ 2 + z.b ^ 2 ≠ 0 := by
        intro hd
        apply hz
        ext
        · have : z.a ^ 2 = 0 := by nlinarith [sq_nonneg z.a, sq_nonneg z.b, hd]
          exact sq_eq_zero_iff.mp this
        · have : z.b ^ 2 = 0 := by nlinarith [sq_nonneg z.a, sq_nonneg z.b, hd]
          exact sq_eq_zero_iff.mp this
      field_simp [hd] at h'
      exact h'.symm
    -- 目标 norm (z - lift(1/2)) = (1/2)²: 
    -- (z.a - 1/2)² + z.b² = 1/4 ⟸ z.a²+z.b² = z.a: 
    simp [norm, lift]
    nlinarith


/-- 非平凡零点 (猜想) 在实数轴 0 点视角下 = 临界线圆上的点:
proj z = 1/2 ∧ z.b ≠ 0 (假复数轴 1/2 + 真复数轴非零) ⟹ recip z ∈ criticalCircle
(圆心 (1,0) 半径 1 的圆)。 -/
theorem nontrivial_zero_on_circle (z : ComplexAxis) (hz : proj z = 1 / 2 ∧ z.b ≠ 0) :
    recip z ∈ criticalCircle := by
  exact critical_line_in_circle z hz.1


/-! ## 圆的配对: 全部交点的 Lean 形式化

四个对象 (素数圆、临界线圆、半圆、实轴) 的两两配对:
  * 半圆 ∩ 临界线圆 = {0} (在真 0 点内切, halfCircle_inter_criticalCircle);
  * 半圆 ∩ 实轴 = {0, 1} (realAxis_inter_halfCircle);
  * 素数圆 ∩ 半圆 = ∅ (p ≥ 2 不相交, primeCircle_disjoint_halfCircle);
  * 素数圆 ∩ 实轴 = {±√p} (primeCircle_inter_realAxis);
  * 素数圆 ∩ 临界线圆 ⟹ p ≤ 4 (primeCircle_inter_criticalCircle_bounded);
  * 临界线圆 ∩ 实轴 = {0, 2} (realAxis_inter_criticalCircle, C020)。 -/

/-- 假复数轴 1/2 位置的圆: 圆心 (1/2,0) 半径 1/2 (经过真 0 点)。 -/
def halfCircle : Set ComplexAxis :=
  {z : ComplexAxis | norm (z - lift (1 / 2)) = (1 / 2 : ℝ) ^ 2}

/-- 半圆经过真 0 点: 0 ∈ halfCircle。 -/
theorem zero_in_halfCircle : (0 : ComplexAxis) ∈ halfCircle := by
  simp [halfCircle, norm, lift]

/-- 半圆与实轴的交点: lift r ∈ halfCircle ⟺ r = 0 ∨ r = 1。 -/
theorem realAxis_inter_halfCircle (r : ℝ) :
    lift r ∈ halfCircle ↔ r = 0 ∨ r = 1 := by
  constructor
  · intro h
    have h' : (r - 1 / 2) ^ 2 = (1 / 2 : ℝ) ^ 2 := by simpa [halfCircle, norm, lift] using h
    have : r - 1 / 2 = 1 / 2 ∨ r - 1 / 2 = -(1 / 2) := by
      have h1 : |r - 1 / 2| = |1 / 2| := (sq_eq_sq_iff_abs_eq_abs (r - 1 / 2) (1 / 2)).1 h'
      exact (abs_eq_abs).1 h1
    rcases this with h1 | h2
    · right
      linarith
    · left
      linarith
  · rintro (h0 | h1)
    · rw [h0]
      simp [halfCircle, norm, lift]
    · rw [h1]
      simp [halfCircle, norm, lift]
      norm_num

/-- 半圆与临界线圆只在真 0 点相交 (内切):
z ∈ halfCircle ∧ z ∈ criticalCircle ⟺ z = 0。 -/
theorem halfCircle_inter_criticalCircle (z : ComplexAxis) :
    z ∈ halfCircle ∧ z ∈ criticalCircle ↔ z = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (z.a - 1 / 2) ^ 2 + z.b ^ 2 = (1 / 2 : ℝ) ^ 2 := by
      simpa [halfCircle, norm, lift] using h1
    have h2' : (z.a - 1) ^ 2 + z.b ^ 2 = 1 := by
      simpa [criticalCircle, norm, lift] using h2
    have ha : z.a = 0 := by nlinarith
    have hb : z.b = 0 := by
      have : z.b ^ 2 = 0 := by nlinarith [ha, h1']
      exact sq_eq_zero_iff.mp this
    ext <;> simp [ha, hb]
  · rintro rfl
    constructor
    · simp [halfCircle, norm, lift]
    · simp [criticalCircle, norm, lift]

/-- 素数圆与半圆不相交 (p ≥ 2): z ∈ primeCircle p ∧ z ∈ halfCircle ⟹ False。 -/
theorem primeCircle_disjoint_halfCircle (p : ℕ) (hp : 2 ≤ p) (z : ComplexAxis)
    (h1 : z ∈ primeCircle p) (h2 : z ∈ halfCircle) : False := by
  have hnz : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [primeCircle, norm] using h1
  have hnw : (z.a - 1 / 2) ^ 2 + z.b ^ 2 = (1 / 2 : ℝ) ^ 2 := by
    simpa [halfCircle, norm, lift] using h2
  have ha : z.a = (p : ℝ) := by nlinarith
  have ha2 : z.a ^ 2 ≤ (p : ℝ) := by nlinarith [sq_nonneg z.b, hnz]
  have hp2 : (p : ℝ) ≤ 1 := by
    have hnw' : z.a ^ 2 ≤ z.a := by nlinarith [sq_nonneg z.b, hnw]
    have : (p : ℝ) ^ 2 ≤ (p : ℝ) := by
      rwa [ha] at hnw'
    nlinarith [sq_nonneg (p : ℝ), this]
  have hp1 : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  nlinarith

/-- 素数圆与实轴的交点: z ∈ primeCircle p ∧ z.b = 0 ⟺ z = lift(√p) ∨ z = lift(−√p)。 -/
theorem primeCircle_inter_realAxis (p : ℕ) (z : ComplexAxis) :
    z ∈ primeCircle p ∧ z.b = 0 ↔ z = lift (Real.sqrt p) ∨ z = lift (-Real.sqrt p) := by
  constructor
  · rintro ⟨h1, hb⟩
    have hnz : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [primeCircle, norm] using h1
    have ha2 : z.a ^ 2 = (p : ℝ) := by
      rw [hb] at hnz
      nlinarith
    have hsq : z.a ^ 2 = (Real.sqrt (p : ℝ)) ^ 2 := by
      rw [ha2]
      rw [Real.sq_sqrt (by exact_mod_cast (Nat.zero_le p) : 0 ≤ (p : ℝ))]
    have : z.a = Real.sqrt (p : ℝ) ∨ z.a = -Real.sqrt (p : ℝ) := by
      have h1 : |z.a| = |Real.sqrt (p : ℝ)| := (sq_eq_sq_iff_abs_eq_abs z.a (Real.sqrt (p : ℝ))).1 hsq
      exact (abs_eq_abs).1 h1
    rcases this with h | h
    · left
      ext <;> simp [lift, h, hb]
    · right
      ext <;> simp [lift, h, hb]
  · rintro (h | h)
    · rw [h]
      simp [primeCircle, norm, lift, Real.sq_sqrt (by exact_mod_cast (Nat.zero_le p) : 0 ≤ (p : ℝ))]
    · rw [h]
      simp [primeCircle, norm, lift, Real.sq_sqrt (by exact_mod_cast (Nat.zero_le p) : 0 ≤ (p : ℝ))]

/-- 素数圆与临界线圆相交 ⟹ p ≤ 4 (圆心距 1, 半径 √p 和 1 的相交条件)。 -/
theorem primeCircle_inter_criticalCircle_bounded (p : ℕ) (z : ComplexAxis)
    (h1 : z ∈ primeCircle p) (h2 : z ∈ criticalCircle) : p ≤ 4 := by
  have hnz : z.a ^ 2 + z.b ^ 2 = (p : ℝ) := by simpa [primeCircle, norm] using h1
  have : z.a = (p : ℝ) / 2 := by
    have : proj z = (p : ℝ) / 2 := inter_proj p z h1 h2
    simpa [proj] using this
  have hb2 : 0 ≤ z.b ^ 2 := sq_nonneg z.b
  have hbound : (p : ℝ) ≤ 4 := by
    nlinarith
  exact_mod_cast hbound


/-! ## 非平凡零点的形状: 两个视角

非平凡零点 (猜想) 在两个轴视角下的形状 (OBSERVATION/KNOWN):
  * 假复数轴视角 (未蜷曲): 竖直线 (临界线 x = 1/2) — critical_line_points /
    nontrivial_zero_position (已证);
  * 反演轴视角 (蜷曲, 实数 0 点): 圆 (圆心 (1,0) 半径 1) — 
    nontrivial_zero_on_circle (已证)。
本节的补充: recip_involutive (反演对合: 形状变换的核心性质),
circle_recip_proj (圆上非 0 点反演后回到临界线 — 反向形状),
critical_line_image_subset_circle (集合版)。 -/

/-- 反演对合: recip (recip z) = z (z ≠ 0) — 蜷曲操作两次回到自身。 -/
theorem recip_involutive (z : ComplexAxis) (hz : z ≠ 0) : recip (recip z) = z := by
  cases z with
  | mk a b =>
    have hsq : a ^ 2 + b ^ 2 ≠ 0 := by
      intro h
      apply hz
      ext
      · have : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
        exact sq_eq_zero_iff.mp this
      · have : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
        exact sq_eq_zero_iff.mp this
    ext
    · simp [recip]
      field_simp [hsq]
    · simp [recip]
      field_simp [hsq]

/-- 反演轴视角的反向形状: 临界线圆上非 0 的点 w, 反演后落在临界线上:
norm (w - lift 1) = 1 ∧ w ≠ 0 ⟹ proj (recip w) = 1/2。 -/
theorem circle_recip_proj (w : ComplexAxis) (hw : norm (w - lift 1) = 1)
    (hw0 : w ≠ 0) : proj (recip w) = 1 / 2 := by
  cases w with
  | mk a b =>
    have h' : (a - 1) ^ 2 + b ^ 2 = 1 := by simpa [norm, lift] using hw
    have hsum : a ^ 2 + b ^ 2 = 2 * a := by nlinarith
    have ha0 : a ≠ 0 := by
      intro ha
      have : b ^ 2 = 0 := by
        rw [ha] at hsum
        nlinarith [sq_nonneg b, hsum]
      have hb : b = 0 := sq_eq_zero_iff.mp this
      apply hw0
      ext <;> simp [ha, hb]
    change proj (recip ⟨a, b⟩) = 1 / 2
    simp [proj, recip]
    rw [hsum]
    field_simp [ha0]

/-- 集合版: 非平凡零点 (猜想) 在反演轴视角下落入临界线圆 —
recip '' {z | proj z = 1/2 ∧ z.b ≠ 0} ⊆ criticalCircle。 -/
theorem critical_line_image_subset_circle :
    recip '' {z : ComplexAxis | proj z = 1 / 2 ∧ z.b ≠ 0} ⊆ criticalCircle := by
  intro w hw
  rcases hw with ⟨z, hz, rfl⟩
  exact nontrivial_zero_on_circle z hz


/-! ## 非平凡零点的圆 = 临界线圆 (同一个圆)

"非平凡零点 (猜想) 所在之圆" 与 "临界线圆" 是同一个对象 (criticalCircle,
圆心 (1,0) 半径 1): 零点集的 recip 像 ⊆ 临界线圆, 且临界线圆上非平凡
点 (≠ 0, ≠ 2; 0 = ∞ 的像, 2 = 平凡点 1/2 的像) 都是某零点位置的像。
(OBSERVATION/KNOWN。) -/

/-- 非平凡零点 (猜想) 的位置集: 假复数轴 1/2 + 真复数轴非零
(临界线去实点)。 -/
def nontrivialZeroSet : Set ComplexAxis :=
  {z : ComplexAxis | proj z = 1 / 2 ∧ z.b ≠ 0}

/-- 零点集在反演下落入临界线圆: z ∈ nontrivialZeroSet ⟹ recip z ∈ criticalCircle
(非平凡零点的圆 ⊆ 临界线圆)。 -/
theorem zeroSet_in_criticalCircle (z : ComplexAxis) (hz : z ∈ nontrivialZeroSet) :
    recip z ∈ criticalCircle := by
  exact nontrivial_zero_on_circle z hz

/-- 临界线圆上非平凡点 (≠ 0, ≠ 2) 都是某零点位置的 recip 像:
criticalCircle 上非 0 非 2 的点 w ⟹ w ∈ recip '' nontrivialZeroSet
(临界线圆 ⊆ 非平凡零点的圆)。 -/
theorem criticalCircle_subset_zeroSet_image (w : ComplexAxis)
    (hw : w ∈ criticalCircle) (hw0 : w ≠ 0) (hw2 : w ≠ lift 2) :
    w ∈ recip '' nontrivialZeroSet := by
  refine ⟨recip w, ?_, ?_⟩
  · constructor
    · exact circle_recip_proj w hw hw0
    · intro hb
      cases w with
      | mk a b =>
        have hsq : a ^ 2 + b ^ 2 ≠ 0 := by
          intro h
          apply hw0
          ext
          · have : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
            exact sq_eq_zero_iff.mp this
          · have : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
            exact sq_eq_zero_iff.mp this
        have hb' : b = 0 := by
          simp [recip] at hb
          rcases hb with hb0 | hsq0
          · exact hb0
          · exact False.elim (hsq hsq0)
        have hw' : (a - 1) ^ 2 = 1 := by
          have h'' : (a - 1) ^ 2 + b ^ 2 = 1 := by simpa [criticalCircle, norm, lift] using hw
          nlinarith [hb']
        have ha : a = 0 ∨ a = 2 := by
          have : a - 1 = 1 ∨ a - 1 = -1 := by
            have h1 : |a - 1| = |1| := (sq_eq_sq_iff_abs_eq_abs (a - 1) 1).1 (by simpa using hw')
            exact (abs_eq_abs).1 h1
          rcases this with h1 | h2
          · right
            linarith
          · left
            linarith
        rcases ha with ha0 | ha2
        · apply hw0
          ext <;> simp [ha0, hb']
        · apply hw2
          ext <;> simp [ha2, hb', lift]
  · exact recip_involutive w hw0


/-! ## 素数圆 8 整点成对: 4 个共轭对

素数 p ≡ 1 (mod 4) 的圆上 8 个整点是成对的 — 4 个共轭对 (关于假复数轴
镜像): (a,b)↔(a,-b), (-a,b)↔(-a,-b), (b,a)↔(b,-a), (-b,a)↔(-b,-a)。
每对 = {z, conj z}, 对合 (conj (conj z) = z), 且都在同一圆上
(norm_conj)。加上 90° 旋转 4 循环 (rot90_four), 8 点 = 4 对 × 2 半圈。
(OBSERVATION/KNOWN。) -/

/-- 共轭对合: conj (conj z) = z — 镜像两次回到自身 (成对的基础)。 -/
theorem conj_involutive (z : ComplexAxis) : conj (conj z) = z := by
  ext <;> simp [conj]

/-- 共轭对: conj ⟨a,b⟩ = ⟨a,-b⟩ — 8 整点中每对由镜像 (conj) 连接,
关于假复数轴对称。 -/
theorem conj_pair (a b : ℝ) : conj (⟨a, b⟩ : ComplexAxis) = ⟨a, -b⟩ := by
  simp [conj]


/-! ## 素数圆转一圈的乘积: 8 整点乘积 = p⁴

素数圆上 8 个整点 {±z, ±z̄, ±iz, ±iz̄} 两两共轭配对, 每对乘积 = 范数 p:
z·z̄ = |z|² = p。4 对 × p = p⁴ — 转一圈 (90° 旋转 4 循环 + 共轭镜像)
乘完是 p⁴, 与方向无关。 (OBSERVATION/KNOWN: 范数乘性/共轭对。) -/

/-- 共轭对乘积 = 范数: z * conj z = lift (norm z)。 -/
theorem mul_conj (z : ComplexAxis) : z * conj z = lift (norm z) := by
  ext <;> simp [mul, conj, norm, lift] <;> ring

/-- 素数的共轭对乘积: norm z = p ⟹ z * conj z = lift p。 -/
theorem prime_conj_pair (z : ComplexAxis) (hz : norm z = (p : ℝ)) :
    z * conj z = lift (p : ℝ) := by
  rw [mul_conj, hz]

/-- 旋转的共轭对乘积: (iz)·conj(iz) = lift p — 转一圈中每对仍是范数。 -/
theorem rotated_conj_pair (z : ComplexAxis) (hz : norm z = (p : ℝ)) :
    (rot90 z) * conj (rot90 z) = lift (p : ℝ) := by
  rw [mul_conj]
  rw [rot90_norm, hz]


/-! ## i 的后继乘法表: 每两个 = -1

i 的后继迭代 (×i 打转): 1, i, -1, -i, 1 — 每两步乘出 -1 (J² = -1,
半圈 = 180° 旋转, C011 J_sq; 旋转循环 rot90_sq: R² = -z)。 -/

/-- i² = -1: i 的后继每两个乘出 -1 (npow 版本)。 -/
theorem J_pow_two : npow J 2 = -1 := by
  change npow J 2 = neg one
  ext <;> simp [npow, J, one, mul, neg] <;> ring

/-- i⁴ = 1: 转一圈回到自身 (4 循环乘法表闭合)。 -/
theorem J_pow_four : npow J 4 = 1 := by
  change npow J 4 = one
  ext <;> simp [npow, J, one, mul, neg] <;> ring

/-- 旋转两步 = ×(-1): rot90 (rot90 z) = -z — 素数圆转一圈中
每两个后继 = -1。 -/
theorem rotate_two_neg (z : ComplexAxis) : rot90 (rot90 z) = -z := by
  change rot90 (rot90 z) = neg z
  ext <;> simp [rot90, neg] <;> ring


/-! ## 分裂结构的几何版: 8 点 = 高斯素数 π 的伴随集

p ≡ 1 (mod 4) 素数在高斯整数中分裂: p = π·π̄ (π = a+bi 高斯素数,
共轭对 prime_conj_pair)。8 个整点 = π 的 4 个伴随 (乘乘性单位
{±1, ±J}) ∪ π̄ 的 4 个伴随:
  {±z, ±J·z} ∪ {±conj z, ±J·conj z}
伴随保范数 (单位范数 = 1, norm_mul) — 每个伴随仍在圆上。
这是复平面 (高斯数域) 欧拉乘积的构件: p 分裂为一对共轭高斯素数。
(OBSERVATION/KNOWN: 高斯整数分裂/伴随。) -/

/-- 乘性单位 (i 的后继表): {1, -1, J, -J}。 -/
def isUnit4 (u : ComplexAxis) : Prop := u = 1 ∨ u = -1 ∨ u = J ∨ u = -J

/-- 高斯素数 z 的伴随集: z 乘乘性单位 {±1, ±J}。 -/
def associates (z : ComplexAxis) : Set ComplexAxis :=
  {w : ComplexAxis | ∃ u : ComplexAxis, isUnit4 u ∧ w = z * u}

/-- 单位范数 = 1: norm u = 1 (u ∈ {±1, ±J})。 -/
theorem norm_unit4 (u : ComplexAxis) (hu : isUnit4 u) : norm u = 1 := by
  rcases hu with rfl | rfl | rfl | rfl
  · norm_num [norm, one]
  · change norm (neg one) = 1
    norm_num [norm, one, neg]
  · norm_num [norm, J]
  · change norm (neg J) = 1
    norm_num [norm, J, neg]

/-- 伴随保范数: w ∈ associates z ⟹ norm w = norm z — 每个伴随仍在圆上。 -/
theorem associates_norm (z w : ComplexAxis) (hw : w ∈ associates z) : norm w = norm z := by
  rcases hw with ⟨u, hu, rfl⟩
  rw [norm_mul, norm_unit4 u hu, mul_one]

/-- 8 变体 = 伴随并集: 符号×顺序变体恰好 = {±z, ±J·z} ∪ {±conj z, ±J·conj z}
(π 的 4 伴随 ∪ π̄ 的 4 伴随)。 -/
theorem variants_are_associates (a b : ℝ) :
    ⟨a, -b⟩ ∈ associates (conj (⟨a, b⟩ : ComplexAxis)) ∧
      ⟨-a, b⟩ ∈ associates (conj (⟨a, b⟩ : ComplexAxis)) ∧
      ⟨-a, -b⟩ ∈ associates (⟨a, b⟩ : ComplexAxis) ∧
      ⟨b, a⟩ ∈ associates (conj (⟨a, b⟩ : ComplexAxis)) ∧
      ⟨b, -a⟩ ∈ associates (⟨a, b⟩ : ComplexAxis) ∧
      ⟨-b, a⟩ ∈ associates (⟨a, b⟩ : ComplexAxis) ∧
      ⟨-b, -a⟩ ∈ associates (conj (⟨a, b⟩ : ComplexAxis)) := by
  constructor
  · refine ⟨1, Or.inl rfl, ?_⟩
    ext <;> simp [conj, mul, one]
  constructor
  · refine ⟨-1, Or.inr (Or.inl rfl), ?_⟩
    change ⟨-a, b⟩ = conj (⟨a, b⟩ : ComplexAxis) * neg one
    ext <;> simp [conj, mul, neg, one] <;> ring
  constructor
  · refine ⟨-1, Or.inr (Or.inl rfl), ?_⟩
    change ⟨-a, -b⟩ = (⟨a, b⟩ : ComplexAxis) * neg one
    ext <;> simp [mul, neg, one] <;> ring
  constructor
  · refine ⟨J, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    ext <;> simp [conj, J, mul, one] <;> ring
  constructor
  · refine ⟨-J, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    change ⟨b, -a⟩ = (⟨a, b⟩ : ComplexAxis) * neg J
    ext <;> simp [J, mul, neg, one] <;> ring
  constructor
  · refine ⟨J, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    ext <;> simp [J, mul, one] <;> ring
  · refine ⟨-J, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    change ⟨-b, -a⟩ = conj (⟨a, b⟩ : ComplexAxis) * neg J
    ext <;> simp [conj, J, mul, neg, one] <;> ring

/-! ## 真 0 点视角: 素数圆 8 整点的 recip 乘积 = 1/p⁴

真 0 点视角 = 反演 (recip)。8 个整点 {±z, ±z̄, ±Jz, ±Jz̄} 反演后:
{±1/z, ±1/z̄, ±1/(Jz), ±1/(Jz̄)} — 仍是 4 对共轭, 每对乘积:
recip z · recip z̄ = recip(z·z̄) = recip p = 1/p (recip_mul + prime_conj_pair +
recip_lift)。四对 × 1/p = 1/p⁴ — 与未反演视角 (p⁴, C023) 互为倒数。
(OBSERVATION/KNOWN: 反演保共轭对结构。) -/

/-- 反演与共轭交换: conj (recip z) = recip (conj z) (z ≠ 0)。 -/
theorem conj_recip (z : ComplexAxis) (hz : z ≠ 0) : conj (recip z) = recip (conj z) := by
  cases z with
  | mk a b =>
    have hsq : a ^ 2 + b ^ 2 ≠ 0 := by
      intro h
      apply hz
      ext
      · have : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
        exact sq_eq_zero_iff.mp this
      · have : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
        exact sq_eq_zero_iff.mp this
    ext <;> simp [recip, conj] <;> field_simp [hsq] <;> ring

/-- 真 0 点视角的共轭对: norm z = p ⟹ recip z · recip (conj z) = lift (1/p)
(反演后每对仍是 1/p — 与未反演视角 (共轭对 = p) 互为倒数)。 -/
theorem recip_conj_pair (z : ComplexAxis) (hz : z ≠ 0) (hp : norm z = (p : ℝ)) :
    recip z * recip (conj z) = lift (1 / (p : ℝ)) := by
  cases z with
  | mk a b =>
    have hsq : a ^ 2 + b ^ 2 ≠ 0 := by
      intro h
      apply hz
      ext
      · have : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
        exact sq_eq_zero_iff.mp this
      · have : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
        exact sq_eq_zero_iff.mp this
    have hD : a ^ 2 + b ^ 2 = (p : ℝ) := by simpa [norm] using hp
    ext
    · simp [recip, conj, mul, lift]
      field_simp [hsq]
      have hp0 : (p : ℝ) ≠ 0 := by
        intro h
        apply hsq
        rw [hD, h]
      have : a ^ 2 + b ^ 2 = (a ^ 2 + b ^ 2) ^ 2 / (p : ℝ) := by
        rw [hD]
        field_simp [hp0]
      simpa using this
    · change (recip (⟨a, b⟩ : ComplexAxis) * recip (conj (⟨a, b⟩ : ComplexAxis))).b = 0
      simp [recip, conj, mul]
      field_simp [hsq]
      ring


/-! ## 真 0 点视角: 复数的次方与二阶乘性反轴

1. 8 点 recip 乘积 = 1/p⁴ = p⁻⁴ — 复数 p 的 -4 次方 (recip_conj_pair
   逐对: 每对 = 1/p, 四对 = 1/p⁴; 与未反演视角 p⁴ (C023) 互为倒数)。
2. recip 是"以 0 为原点的二阶乘性反轴":
   - 二阶 (对合): recip² = id (recip_involutive);
   - 乘性反向: |recip z| = 1/|z| (norm_recip) — 模长轴 r ↦ 1/r;
   - 数轴上: lift r ↦ lift (1/r) (recip_lift) — 方向反向。
   (OBSERVATION/KNOWN。) -/

/-- 0 点视角的乘性反轴: recip 是二阶 (对合) 乘性反演 —
模长轴方向反向 (|recip z| = 1/|z|), 两次回到自身。 -/
theorem recip_axis_second_order (z : ComplexAxis) (hz : z ≠ 0) :
    recip (recip z) = z ∧ norm (recip z) = 1 / norm z := by
  constructor
  · exact recip_involutive z hz
  · exact norm_recip z

/-- 真 0 点视角: 素数圆整点反演后共轭对 = 1/p (每对), 四对 = 1/p⁴ =
p⁻⁴ — 复数的负次方 (与 C023 的 p⁴ 互为倒数)。 -/
theorem zero_point_prime_pair (z : ComplexAxis) (hz : z ≠ 0) (hp : norm z = (p : ℝ)) :
    recip z * recip (conj z) = lift (1 / (p : ℝ)) :=
  recip_conj_pair z hz hp


/-! ## 临界线在 0 点视角乘性轴上的形状

临界线 (竖直线 x = 1/2) 在 0 点视角 (recip) 下 = 圆心 (1,0) 半径 1 的圆
(critical_line_is_circle), 穿过乘性反轴 (实轴) 上的两点:
  0 (∞ 卷回点, recip 奇点) 和 2 (1/2 的反演像)。
圆 ∩ 实轴 = {0, 2} (realAxis_inter_criticalCircle)。 -/

/-- 0 点视角: 临界线圆穿过乘性轴上的 0 和 2, 且圆与乘性轴的交点
恰好是这两点 — 竖直线经 recip 卷成环, 钉在轴上的 0 和 2。 -/
theorem critical_line_circle_on_recip_axis :
    (0 : ComplexAxis) ∈ criticalCircle ∧ lift 2 ∈ criticalCircle ∧
      (∀ z : ComplexAxis, z ∈ criticalCircle ∧ z.b = 0 → z = 0 ∨ z = lift 2) := by
  constructor
  · exact zero_in_criticalCircle
  · constructor
    · simp [criticalCircle, norm, lift]
      norm_num
    · intro z hz
      have : ∃ r : ℝ, z = lift r := (real_axis_points z).1 hz.2
      rcases this with ⟨r, rfl⟩
      rcases (realAxis_inter_criticalCircle r).1 hz.1 with h0 | h2
      · left
        ext <;> simp [lift, h0, zero]
      · right
        ext <;> simp [lift, h2, zero]


/-! ## 计算工具在 0 点视角: 交替级数 (η) 与函数方程

非平凡零点的数值计算工具 (复平面视角) 在 0 点视角下:
  1. 交替级数 (η): ζ(s) = (1 - 2^{1-s})⁻¹ · Σ (-1)^{n-1}/n^s —
     每项 1/n^s = recip (npow (lift n) s) (zetaTerm, 0 点视角的蜷曲),
     交替符号 ×(-1) = i 的后继 (每两个 = -1); 因子
     (1 - 2^{1-s})⁻¹ = recip 结构。
  2. 黎曼-西格尔公式: 基于函数方程 ξ(s) = ξ(1-s) — 0 点视角构件
     已形式化: s ↦ 1-s 反射 = reflectSqrt 的平方 (C018), 临界线上
     1-s = conj s (critical_line_iff_conj), 竖线蜷曲成圆 (C019)。 -/

/-- 交替级数项 (η 的 0 点视角): (-1)^n · 1/(n+1)^s —
整数位的 recip (0 点蜷曲) 乘交替符号 (i 的后继 ×(-1))。 -/
noncomputable def etaTerm (n s : ℕ) : ComplexAxis :=
  npow (lift (-1)) n * recip (npow (lift (n + 1 : ℕ)) s)

/-- η 项 = 交替符号 × zetaTerm (0 点视角: 每项是整数位的 recip)。 -/
theorem etaTerm_eq (n s : ℕ) : etaTerm n s = npow (lift (-1)) n * zetaTerm n s := by
  rfl

/-- 交替符号是 i 的后继: (lift (-1))^2 = lift 1 — 每两步回到正号
(半圈 = ×(-1), J_pow_two 的实轴版本)。 -/
theorem alt_sign_period2 (n : ℕ) : npow (lift (-1)) (n + 2) = npow (lift (-1)) n := by
  -- (lift (-1))^(n+2) = (lift (-1))^n · (lift (-1))^2 = ... · 1: 需要结合律 — 分量算: 
  -- 直接: (-1)^(n+2) = (-1)^n (ℝ): 
  -- 用 npow 展开: 分量计算: 
  ext <;> simp [npow, lift, mul, neg, one]


/-! ## 把基点移动到 Re = 1/2 (视角变换, 纯几何)

在假复数轴上把基点移动到 1/2 位置: 基点可以是整条临界线
(投影压缩, 等价类, C011)。注意: 这是视角变换 — 不改变 ζ 的零点
位置 (那是分析事实, 几何重述不产生新信息)。 -/

/-- 基点: 假复数轴 1/2 位置。 -/
noncomputable def halfBasepoint : ComplexAxis := lift (1 / 2)

/-- 基点投影 = 1/2。 -/
theorem halfBasepoint_proj : proj halfBasepoint = 1 / 2 := by
  simp [halfBasepoint, proj, lift]

/-- 基点落在临界线: lift(1/2) ∈ {z | proj z = 1/2}。 -/
theorem halfBasepoint_on_critical_line :
    halfBasepoint ∈ {z : ComplexAxis | proj z = 1 / 2} := by
  simp [halfBasepoint, proj, lift]

/-- 基点可以是整条临界线: 临界线 {lift(1/2) + t·J} 上每一点的投影
都是 1/2 (critical_line_points) — 基点 lift(1/2) 是这族投影等价
基点的一员 (投影压缩丢失结构, C011)。 -/
theorem basepoint_is_critical_line_family :
    ∀ t : ℝ, proj (lift (1 / 2) + lift t * J) = 1 / 2 := by
  intro t
  exact (critical_line_points (lift (1 / 2) + lift t * J)).2 ⟨t, rfl⟩

/-- 基点漂移: 从原点 0 到 1/2 — 平移 lift (1/2) (视角变换)。 -/
theorem basepoint_drift_to_half : halfBasepoint = lift 0 + lift (1 / 2) := by
  rw [halfBasepoint, ← lift_add]
  norm_num [lift]


/-! ## 新基点视角: 实部轴 (Re) 的形状

基点 halfBasepoint = lift(1/2) 仍是复平面上的点。新视角下实部轴 (Re)
= 过基点的实方向线 {lift(1/2) + lift t}: 投影压掉真复数轴 (J 方向)
后仍是整条实轴 (平移 1/2)。0 点视角 (recip): 基点 → 2 (临界线圆与
乘性轴的交点), 实部轴在蜷曲下是黎曼球面的大圆 (乘性反轴 r ↦ 1/r)。 -/

/-- 新基点视角的实部轴 (Re): 过基点 lift(1/2) 的实方向线。 -/
def realAxisAtHalf : Set ComplexAxis :=
  {z : ComplexAxis | ∃ t : ℝ, z = lift (1 / 2) + lift t}

/-- 基点在新实部轴上: halfBasepoint ∈ realAxisAtHalf。 -/
theorem halfBasepoint_in_realAxisAtHalf : halfBasepoint ∈ realAxisAtHalf := by
  refine ⟨0, ?_⟩
  rw [halfBasepoint, ← lift_add]
  norm_num [lift]

/-- 新实部轴的投影 = 整条实轴 (平移 1/2): 真复数轴 (J 方向) 被投影
压掉, 剩下的是完整实轴 — Re 在新基点视角是一条线。 -/
theorem realAxisAtHalf_proj (t : ℝ) :
    proj (lift (1 / 2) + lift t) = 1 / 2 + t := by
  simp [proj, lift, add]

/-- 0 点视角: 基点 1/2 反演后 = 2 (临界线圆与乘性轴的交点)。 -/
theorem halfBasepoint_recip : recip halfBasepoint = lift 2 := by
  rw [halfBasepoint]
  have h : (1 / 2 : ℝ) ≠ 0 := by norm_num
  rw [recip_lift (1 / 2) h]
  norm_num [lift]

/-- 0 点视角: 新实部轴上的点在乘性反轴上的像: recip 把 (1/2 + t) 映到
1/(1/2 + t) — 实部轴在蜷曲下是乘性反轴 (r ↦ 1/r), 加 ∞ 成黎曼球面
大圆。 -/
theorem realAxisAtHalf_recip (t : ℝ) (ht : lift (1 / 2) + lift t ≠ 0) :
    recip (lift (1 / 2) + lift t) = lift (1 / (1 / 2 + t)) := by
  have hsum : lift (1 / 2) + lift t = lift (1 / 2 + t) := by
    rw [← lift_add]
  have h0 : 1 / 2 + t ≠ 0 := by
    intro h
    apply ht
    rw [hsum]
    ext
    · simp [lift]
      norm_num at h ⊢
      exact h
    · simp [lift]
  rw [hsum]
  exact recip_lift (1 / 2 + t) h0


/-! ## 彻底一维化: 投影压掉真复数轴

新基点视角下 Re 的形状 = 过 1/2 的实方向线 (投影覆盖整条实轴)。
彻底一维化 = proj: 丢真复数轴 (J 方向) 和所有其他结构, 只剩实部 ℝ。
-/

/-- proj 是满射: 每个实数 r 都是某点的投影 (z = lift r) — 一维视图
覆盖全部实数。 -/
theorem proj_surjective (r : ℝ) : ∃ z : ComplexAxis, proj z = r :=
  ⟨lift r, by simp [proj, lift]⟩

/-- proj 的核 = 真复数轴 (J 方向): proj z = 0 ⟺ z = b·J (纯虚方向) —
一维化丢掉的结构正是整个真复数轴。 -/
theorem proj_kernel_J (z : ComplexAxis) : proj z = 0 ↔ ∃ b : ℝ, z = lift b * J := by
  constructor
  · intro h
    refine ⟨z.b, ?_⟩
    ext
    · have : z.a = 0 := by simpa [proj] using h
      simp [lift, J, mul, this]
    · simp [lift, J, mul]
  · rintro ⟨b, rfl⟩
    simp [proj, lift, J, mul]

/-- 彻底一维化: 投影只留实部, 压掉 J 方向 — ComplexAxis 的一维视图
(先投影再抬升回到同一实部)。 -/
theorem dimension_one (z : ComplexAxis) : proj (lift (proj z)) = proj z := by
  simp [proj, lift]


/-! ## 一维化不丢假复数轴结构

proj 压掉真复数轴 (J 方向, proj_kernel_J), 但假复数轴 (lift ℝ) 上的
信息完全保留: 抬升是单射, proj ∘ lift = id (proj_lift) — 投影在
假复数轴上 = 恒等。基点 lift(1/2) 投影清晰可见 (= 1/2,
halfBasepoint_proj)。 -/

/-- 抬升是单射: 假复数轴上不同点投影不同 (信息完整)。 -/
theorem lift_injective (r₁ r₂ : ℝ) : lift r₁ = lift r₂ ↔ r₁ = r₂ := by
  constructor
  · intro h
    have : (lift r₁).a = (lift r₂).a := congrArg ComplexAxis.a h
    simpa [lift] using this
  · intro h
    rw [h]

/-- 假复数轴结构完整保留: 投影在抬升轴上保持 (双射 + 恒等) —
一维化丢的只有 J 方向 (proj_kernel_J), 假复数轴上的信息无损。 -/
theorem real_axis_preserved_by_proj (r₁ r₂ : ℝ) :
    (proj (lift r₁) = proj (lift r₂) ↔ r₁ = r₂) ∧ proj (lift r₁) = r₁ := by
  constructor
  · constructor
    · intro h
      simpa [proj_lift] using h
    · intro h
      rw [h]
  · exact proj_lift r₁

/-- 基点投影清晰可见 (一维化后): proj halfBasepoint = 1/2 —
基点信息完整保留 (与 halfBasepoint_proj 一致)。 -/
theorem halfBasepoint_visible : proj halfBasepoint = 1 / 2 := by
  exact halfBasepoint_proj


/-! ## 投影的还原性: 丢失结构不可还原, 对称性方向可还原

投影 proj 丢失虚轴 (b/J) 分量: 丢失结构不可还原 (i 与 -i 投影相同,
投影值不能唯一确定原像); 但对称性方向可还原 (实轴 ± 对称保留,
lift 单射 + 负号保持)。 -/

/-- 丢失结构不可还原: 不同点可以有相同投影 — i 与 -i 都投影为 0
(原点假象的根源: 基点 i vs -i 无法从投影区分)。 -/
theorem proj_not_recoverable :
    (⟨0, 1⟩ : ComplexAxis) ≠ ⟨0, -1⟩ ∧ proj ⟨0, 1⟩ = proj ⟨0, -1⟩ := by
  constructor
  · intro h
    have hb : (⟨0, 1⟩ : ComplexAxis).b = (⟨0, -1⟩ : ComplexAxis).b := congrArg ComplexAxis.b h
    norm_num at hb
  · simp [proj]

/-- 对称性方向可还原: 投影保留实轴上的 ± 对称 (负号保持) —
实轴方向的对称结构在投影下无损。 -/
theorem proj_recoverable_symmetry (r : ℝ) :
    proj (lift (-r)) = -(proj (lift r)) := by
  simp [proj, lift]

/-- 还原性定理 (打包): 丢失结构不可还原 (虚轴方向, i 与 -i 不可区分),
对称性方向可还原 (实轴 ± 对称, 负号保留)。 -/
theorem projection_recovery_theorem :
    (∃ z₁ z₂ : ComplexAxis, z₁ ≠ z₂ ∧ proj z₁ = proj z₂) ∧
      (∀ r : ℝ, proj (lift (-r)) = -(proj (lift r))) := by
  constructor
  · exact ⟨⟨0, 1⟩, ⟨0, -1⟩, (proj_not_recoverable).1, (proj_not_recoverable).2⟩
  · intro r
    simp [proj, lift]


/-! ## 信息丢失与剩余的势: 可数与不可数

投影核 (J 方向, {z | proj z = 0}) 与剩余 (实轴, {z | z.b = 0}) 都
与 ℝ 等势 (因此不可数, mathlib: not_countable_real) — "可数 vs
不可数"的对比不发生在丢失/剩余之间; 成立的是: 素数 (可数集,
ℕ 子集) vs 圆上连续点 (不可数, ℝ 势)。 -/

/-- 投影核 (J 方向) 与 ℝ 等势: 映射 b ↦ ⟨0,b⟩ 是等价 — 丢失的结构
(虚轴方向) 是不可数势。 -/
noncomputable def kernelEquivReal : {z : ComplexAxis | proj z = 0} ≃ ℝ where
  toFun z := z.1.b
  invFun b := ⟨⟨0, b⟩, by simp [proj]⟩
  left_inv z := by
    rcases z with ⟨⟨a, b⟩, h⟩
    have ha : a = 0 := by simpa [proj] using h
    ext <;> simp [ha]
  right_inv b := rfl

/-- 剩余 (实轴) 与 ℝ 等势: 映射 r ↦ lift r 是等价 — 保留的结构
(实轴) 也是不可数势。 -/
noncomputable def realAxisEquivReal : {z : ComplexAxis | z.b = 0} ≃ ℝ where
  toFun z := z.1.a
  invFun r := ⟨lift r, by simp [lift]⟩
  left_inv z := by
    rcases z with ⟨⟨a, b⟩, h⟩
    have hb : b = 0 := by simpa using h
    ext <;> simp [lift, hb]
  right_inv r := by
    simp [lift]

/-- 素数可数: {p : ℕ | Nat.Prime p} 是 ℕ 的可数子集 — 素数是可数集,
而圆上点是不可数势 (ℝ)。 -/
theorem primes_countable : Countable {p : ℕ | Nat.Prime p} := by
  infer_instance


/-! ## n 基点空间: 语言符号系统的 Lean 模型 (token 设计实验)

语言符号系统建模为 n 基点空间: n 个基点 (锚点, 直觉定义的位置) +
投影 (符号层)。观测/实验 (对应论文第 8 章猜想):
  * 直觉越多 (基点越多), 投影下基点越不可区分 (结构越松散):
    纯虚基点的投影全部相同 (塌缩为一点);
  * 投影值不能还原基点 (歧义): 任意两个不同纯虚基点投影相同;
  * 投影 0 的基点族不可数 (kernelEquivReal) — 信息不足: 单投影值
    无法确定基点。 -/

/-- n 基点空间: n 个基点 (Fin n → ComplexAxis)。 -/
structure BasepointSpace (n : ℕ) where
  basepoints : Fin n → ComplexAxis

/-- 纯虚基点族: 每个基点的实部为 0 (虚轴上, 直觉锚点)。 -/
def pureImagSpace (n : ℕ) : BasepointSpace n where
  basepoints := fun i => ⟨0, (i.1 : ℝ)⟩

/-- 松散性定理: 纯虚基点的投影全部相同 (投影视角下 n 个基点塌缩为
一点) — 直觉 (基点) 越多, 符号层 (投影) 的区分度越低, 结构越松散。 -/
theorem pureImag_collapse (n : ℕ) (i j : Fin n) :
    proj ((pureImagSpace n).basepoints i) = proj ((pureImagSpace n).basepoints j) := by
  simp [pureImagSpace, proj]

/-- 歧义定理: 投影值不能还原基点 — 任意两个不同纯虚基点投影相同
(从 proj 值无法确定是哪个基点, 符号层信息不足)。 -/
theorem basepoint_ambiguity (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    (pureImagSpace n).basepoints i ≠ (pureImagSpace n).basepoints j ∧
      proj ((pureImagSpace n).basepoints i) = proj ((pureImagSpace n).basepoints j) := by
  constructor
  · intro h
    have hb : ((pureImagSpace n).basepoints i).b = ((pureImagSpace n).basepoints j).b :=
      congrArg ComplexAxis.b h
    simp [pureImagSpace] at hb
    apply hij
    exact Fin.ext (by exact_mod_cast hb)
  · exact pureImag_collapse n i j


/-! ## Collapse projection tool: any structure converges to a point

Generalizes proj (kernel = J direction): given carrier S and substructure K,
build projection collapsing K to one point, keeping everything else. -/

/-- Collapse equivalence: two points in K are equivalent (K collapses), outside K identity. -/
def collapseRel (S : Type u) (K : Set S) : S → S → Prop :=
  fun x y => (x ∈ K ∧ y ∈ K) ∨ x = y

/-- Collapse equivalence is an equivalence relation. -/
def collapseSetoid (S : Type u) (K : Set S) : Setoid S where
  r := collapseRel S K
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Or.inr rfl
    · intro x y h
      rcases h with ⟨hx, hy⟩ | hxy
      · exact Or.inl ⟨hy, hx⟩
      · exact Or.inr hxy.symm
    · intro x y z hxy hyz
      rcases hxy with ⟨hx, hy⟩ | hxy
      · rcases hyz with ⟨hy', hz⟩ | hyz
        · exact Or.inl ⟨hx, hz⟩
        · exact Or.inl ⟨hx, by simpa [hyz] using hy⟩
      · rcases hyz with ⟨hy', hz⟩ | hyz
        · exact Or.inl ⟨by simpa [hxy] using hy', hz⟩
        · exact Or.inr (hxy.trans hyz)

/-- Quotient space: S modulo collapse (all points of K identified). -/
def collapseSpace (S : Type u) (K : Set S) : Type u := Quot (collapseRel S K)

/-- Collapse projection: S → quotient. -/
def collapseProj (S : Type u) (K : Set S) : S → collapseSpace S K :=
  Quot.mk (collapseRel S K)

/-- Kernel collapse theorem: any two points of K project identically. -/
theorem collapse_kernel (S : Type u) (K : Set S) {x y : S}
    (hx : x ∈ K) (hy : y ∈ K) :
    collapseProj S K x = collapseProj S K y := by
  exact Quot.sound (Or.inl ⟨hx, hy⟩)

/-! Law (info vs dimension): collapse kernel loses info (kernel points indistinguishable);
quotient's distinguishable points = points outside K + 1. Instances: proj is a special
case of collapseProj (K = J-direction); any segment/polygon/higher-dim structure with
K = whole space collapses to a single point. -/
end ComplexAxis

end ZeroRelative
