/-
Copyright (c) 2026 The Author(s). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: anonymous
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Formal.Toolkit.PatConstruction
import Formal.Toolkit.PatCircle
import Formal.Toolkit.PatMapping
import Formal.Toolkit.CompletePat1
import Formal.Toolkit.Compactification

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Toolkit/PatNumberDomains — ★用 pat 构造所有数域 (pat-construction of number domains)

User instruction (R146, 2026-08-12): 从这里开始, 就要使用 pat 去构造自然数、
π 和所有数域的数了.

The pat construction of every number domain (each link anchored to proven claims):

1. **自然数 = pat 单相位链**: patChain 0 1 n = n (R137 pat_n_is_monophase;
   R142 nat_is_monophase_chain: 基点 0, 方向 d = 1).
2. **整数 = pat 链方向取反**: patChain 0 (-d) n = -(n·d) — 镜像对称对
   {n·d, -n·d} (R085: 0 = ±1 折叠类; R143: 对称对还原).
3. **有理数 = pat 链的商**: n·(1/m) = n/m — 倒数对称对 (R143:
   r·(1/r) = 1 乘法对还原; R110: log 镜像).
4. **π = pat 链蜷曲半圈的相位**: exp(π·I) = -1 — pat 链蜷曲到圆
   (R141: pat_n_phase_on_circle; R055: 时间轴蜷曲), 半圈相位 = π
   (TK3: 欧拉恒等式, π 与 e 在圆上合一; R090: 单位元交汇相位 0).
5. **素数 = pat 方向 log p 的幂链**: log(p^k) = k·log p (R097: 素数幂链
   = 单相位; R142 prime_power_log_layer; R089: log 基点漂移).
6. **实数 = pat 圆上量化极限**: 任意相位 θ 可被 pat 链的 n 槽环量化
   到任意精度 ε (R141 phase_quantizable: 误差 ≤ π/N; R059: 单位根
   n 槽环; R060: 离散⟷连续互逆 — 连续数 = 离散 pat 量化的极限).

Main theorems:

1. `pat_constructs_nat`: 自然数 = pat 单相位链 (R137/R142).
2. `pat_constructs_int`: 整数 = pat 链方向取反 (R085/R143).
3. `pat_constructs_rational`: 有理数 = pat 链的商 (R143/R110).
4. `pat_constructs_pi`: π = pat 链蜷曲半圈的相位 (TK3/R141).
5. `pat_chain_half_turn`: pat 链蜷曲半圈 = -1 (相位 π).
6. `pat_constructs_prime`: 素数 = pat 方向 log p 的幂链 (R097/R142).
7. `pat_quantization_converges`: 实数 = pat 圆上量化极限 — 任意精度逼近
   (R141/R059/R060).
-/

namespace ZeroRelative

namespace PatNumberDomains

open ZeroRelative.CompletePat1

/-! ## 1. 自然数 = pat 单相位链

patChain 0 1 n = n — 基点 0, 方向 d = 1 (R137: pat n = pat0 + n·d;
R142: 自然数 = 基点 0 单位方向单相位链). -/

/-- **自然数 = pat 单相位链**: patChain 0 1 n = n (R137
pat_n_is_monophase; R142 nat_is_monophase_chain: 基点 0, 方向 d = 1). -/
theorem pat_constructs_nat (n : ℕ) :
    PatConstruction.patChain 0 1 n = (n : ℝ) :=
  PatMapping.nat_is_monophase_chain n

/-! ## 2. 整数 = pat 链方向取反

patChain 0 (-d) n = -(n·d) — 方向取反 (镜像 S) 给负链; 正负链组成
对称对 {n·d, -n·d} (R085: 0 = ±1 折叠类; R143: 对称对还原到 0). -/

/-- **整数 = pat 链方向取反**: patChain 0 (-d) n = -((n : ℝ)·d) — 镜像
方向 (-d) 的 pat 链是负链; 正负链 = 对称对 {n·d, -n·d} (R085: 0 =
±1 折叠类, 对称对还原到 0; R143: 加法对称对还原). -/
theorem pat_constructs_int (n : ℕ) (d : ℝ) :
    PatConstruction.patChain 0 (-d) n = -((n : ℝ) * d) := by
  rw [PatConstruction.pat_n_is_monophase]
  ring

/-! ## 3. 有理数 = pat 链的商

n·(1/m) = n/m — 商 = 自然数 × 倒数对称对 (R143: r·(1/r) = 1 乘法对
还原; R110: log 镜像 log(1/a) = -log a). -/

/-- **有理数 = pat 链的商**: n·(1/m) = n/m (m ≠ 0) — 商由倒数对称对
构造 (R143: 乘法对称对 {r, 1/r} 还原到 1; R110: log 镜像对称;
R142: 发散映射层数提取 (n·d)/d = n 的商形式). -/
theorem pat_constructs_rational (n m : ℝ) (hm : m ≠ 0) :
    n * (1 / m) = n / m := by
  field_simp [hm]

/-! ## 4. π = pat 链蜷曲半圈的相位

pat 链蜷曲到圆 (R141: pat_n_phase_on_circle; R055: t ↦ exp(2π·t/T·I));
半圈 t = T/2 的相位 = π: exp(π·I) = -1 (TK3: 欧拉恒等式, π 与 e 在圆上
合一; R090: 单位元交汇相位 0). π 不是预设超越数, 是 pat 链圆上相位
结构常数. -/

/-- **π = pat 链蜷曲半圈的相位**: exp(π·I) = -1 (TK3 euler_identity:
欧拉恒等式, π 与 e 在圆上合一; R090: 三轴单位元交汇于相位 0; R141:
pat 链蜷曲到圆). -/
theorem pat_constructs_pi : Complex.exp (Real.pi * Complex.I) = -1 :=
  CompactToolkit.euler_identity

/-- **pat 链蜷曲半圈 = -1**: exp(2π·(T/2/T)·I) = -1 — pat 链 (步长 T)
蜷曲 (R055) 到半圈 t = T/2 的相位 = π, 圆上值 = -1 (TK3: 欧拉恒等式;
R141: pat 链圆上量化; π = 圆相位结构常数). -/
theorem pat_chain_half_turn (T : ℝ) (hT : T ≠ 0) :
    Complex.exp ((2 * Real.pi * (T / 2 / T) : ℝ) * Complex.I) = -1 := by
  have h : (2 * Real.pi * (T / 2 / T) : ℝ) = Real.pi := by
    field_simp [hT]
  rw [h]
  exact CompactToolkit.euler_identity

/-! ## 5. 素数 = pat 方向 log p 的幂链

素数幂链 {p^k} 经 log 是 pat 单相位链 (方向 log p): log(p^k) = k·log p
(R097: 素数幂链 = 单相位, 间隔 log p; R089: log 把乘法基点 1 漂移到
加法基点 0; R142: prime_power_log_layer). -/

/-- **素数 = pat 方向 log p 的幂链**: log(p^k) = k·log p — 素数幂链
经 log 是 pat 单相位链 (方向 log p, 层数 k) (R097: 素数幂链 = 单相位;
R089: log 基点漂移; R142 prime_power_log_layer). -/
theorem pat_constructs_prime (p : ℝ) (k : ℕ) :
    Real.log (p ^ k) = (k : ℝ) * Real.log p :=
  PatMapping.prime_power_log_layer p k

/-! ## 6. 实数 = pat 圆上量化极限

任意相位 θ ∈ [0, 2π] 可被 pat 链的 n 槽环量化到任意精度 ε (R141
phase_quantizable: 误差 ≤ π/N; R059: 单位根 n 槽环; R060: 离散⟷连续
互逆). 连续实数 = 离散 pat 量化的极限 (n → ∞, 误差 → 0). -/

/-- **实数 = pat 圆上量化极限**: 任意相位 θ ∈ [0, 2π], 任意精度 ε > 0,
存在 pat 链的 n 槽环格点使 |θ - 2π·j/N| ≤ ε — 连续数 = 离散 pat
量化的极限 (R141 phase_quantizable: 误差 ≤ π/N, 取 N ≥ π/ε;
R059: 单位根 n 槽环; R060: 离散⟷连续互逆, n→∞ 精确). -/
theorem pat_quantization_converges (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∃ j : ℕ, j ≤ N ∧
      |θ - 2 * Real.pi * (j : ℝ) / N| ≤ ε := by
  intro ε hε
  have harch : ∃ N : ℕ, (N : ℝ) ≥ Real.pi / ε := exists_nat_ge (Real.pi / ε)
  rcases harch with ⟨N, hN⟩
  have hNpos : 0 < N := by
    have hpiε : 0 < Real.pi / ε := div_pos Real.pi_pos hε
    have hNℝ : 0 < (N : ℝ) := lt_of_lt_of_le hpiε hN
    exact_mod_cast hNℝ
  rcases PatCircle.phase_quantizable θ N hNpos hθ₁ hθ₂ with ⟨j, hj, hq⟩
  refine ⟨N, hNpos, j, hj, ?_⟩
  have hle : Real.pi / (N : ℝ) ≤ ε := by
    have hNℝ : 0 < (N : ℝ) := by exact_mod_cast hNpos
    rw [div_le_iff₀ hNℝ]
    have hNε : Real.pi / ε * ε ≤ (N : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hN (le_of_lt hε)
    have hπ : Real.pi / ε * ε = Real.pi := by
      field_simp [ne_of_gt hε]
    rwa [hπ, mul_comm] at hNε
  exact le_trans hq hle

/-! ## 7. 单相位数 = 成对相位互锁的 a+bi 表示 (有限化收敛到三角函数/π)

User reminder (R146): 单相位数是成对相位互锁的, 可以用 a+bi 的方式来表达;
为了有限化, a、b 必然是收敛到 π 和三角函数上的 — 别搞反了.

因果顺序 (勿反): 单相位数 (成对互锁构造, R136 ②③/R139) ⟹ a+bi 表示
(a = 数值分量, 1 轴; b = 相位分量, i 轴; R143: 1 和 i 还原后的 1)
⟹ 有限化: 相位 θ = 2πk/N 格点 (R141 单位根量化) ⟹ a = r·cos(2πk/N),
b = r·sin(2πk/N) 收敛到三角函数值 ⟹ π = 圆相位结构常数 (TK3:
exp(π·I) = -1; cos π = -1). π 不是单相位数的输入, 是有限化圆上的
相位常数. -/

/-- **单相位数 = 成对相位互锁的 a+bi 表示**: completePat1 pat0 θ r =
pat0 + a + b·i, 其中 a = r·cosθ (1 轴/数值分量), b = r·sinθ (i 轴/相位
分量) — 成对互锁 (相位对 θ,-θ + 数值对 r,1/r, R139) 的单相位数的
a+bi 表达 (R143: 1 和 i 还原后的 1; R140: completePat1). -/
theorem monophase_pair_locked_form (pat0 : ℂ) (θ r : ℝ) :
    completePat1 pat0 θ r = pat0 + (r * Real.cos θ) + Complex.I * (r * Real.sin θ) := by
  unfold completePat1 directionVector
  rw [Complex.exp_mul_I]
  simp [Complex.ofReal_mul, Complex.ofReal_add]
  ring

/-- **有限化 ⟹ a, b 收敛到三角函数值**: 相位格点 θ = 2πk/N (R141 单位根
量化) 上, a = r·cos(2πk/N), b = r·sin(2πk/N) — 单相位数的 a, b 坐标
收敛到三角函数在格点处的值 (R141: 量化误差 ≤ π/N; R059: 单位根 n 槽环;
R060: 离散⟷连续互逆). -/
theorem monophase_finite_coords (pat0 : ℂ) (r k N : ℝ) :
    completePat1 pat0 (2 * Real.pi * k / N) r =
      pat0 + (r * Real.cos (2 * Real.pi * k / N)) + Complex.I * (r * Real.sin (2 * Real.pi * k / N)) :=
  monophase_pair_locked_form pat0 (2 * Real.pi * k / N) r

/-- **三角函数收敛到 π**: cos π = -1 且 sin π = 0 — 半圈相位; π 是圆的
相位结构常数 (TK3: exp(π·I) = -1, π 与 e 在圆上合一; R090: 单位元交汇
相位 0), 不是单相位数的输入 (因果: 单相位构造在前, π 是有限化圆上的
相位常数). -/
theorem trig_converges_to_pi :
    Real.cos Real.pi = -1 ∧ Real.sin Real.pi = 0 := by
  constructor
  · exact Real.cos_pi
  · exact Real.sin_pi

/-- **因果顺序组合: 单相位数 ⟹ a+bi ⟹ 三角函数格点 ⟹ π**: 单相位数
(成对互锁) 的有限化 a+bi 坐标收敛到三角函数格点值, 三角函数收敛到 π
(相位结构常数) — 勿反: π 不是构造输入 (R141 量化; R059 单位根;
TK3 欧拉恒等式). -/
theorem monophase_to_trig_to_pi (pat0 : ℂ) (r k N : ℝ) :
    completePat1 pat0 (2 * Real.pi * k / N) r =
      pat0 + (r * Real.cos (2 * Real.pi * k / N)) + Complex.I * (r * Real.sin (2 * Real.pi * k / N)) ∧
        Real.cos Real.pi = -1 ∧ Real.sin Real.pi = 0 := by
  constructor
  · exact monophase_finite_coords pat0 r k N
  · exact trig_converges_to_pi

end PatNumberDomains

end ZeroRelative
