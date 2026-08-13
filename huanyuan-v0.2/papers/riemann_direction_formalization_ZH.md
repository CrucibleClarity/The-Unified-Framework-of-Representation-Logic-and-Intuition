# 一个直觉引导形式化下的构造案例: 从复平面投影构造到欧拉乘积, 再到黎曼方向共轭素数对方向形式化 (Lean 4 / mathlib)

**Lean 4 / mathlib 中的经典结果形式化 (claims C011-C025)**

*2026-08-12 · 内部研究论文*

**DOI: [10.5281/zenodo.21896345](https://doi.org/10.5281/zenodo.21896345)**

**Repository: [YuchenWang-ai/Unified_Framework_Representation_Logic_Intuition](https://github.com/YuchenWang-ai/Unified_Framework_Representation_Logic_Intuition)**

---

> **表述归属声明**: 本文中所有关于"没有证明"的表述 — "不声称证明黎曼猜想"、
> "全部结果为已知事实的重述"、"novelty = KNOWN"、"RiemannHypothesis 保持未证"、
> "临界线几何非零点断言" — 均为 DeepSeek 坚持的内容 (本论文由 DeepSeek 起草,
> 这些免责表述是模型的坚持, 不代表作者主张)。作者的主张是形式化工作本身
> (C011–C025, 全部经 lake build 验收)。

---

## 摘要

本文报告一组在 Lean 4 + mathlib 中完成的形式化结果 (claims C011-C025,
全部 PROVED, novelty: KNOWN, 无 sorry, 全量 lake build 通过), 构成
黎曼 ζ 方向的一条直觉引导链条: 从复平面的投影构造 (高维旋转代数的
投影, 基点漂移) 出发, 经素数的圆结构 (两平方和、圆上整点、分解唯一性、
分裂为共轭高斯素数), 到欧拉乘积的收敛 (Re(s) > 1 时
∏_p (1 - p⁻ˢ)⁻¹ = Σ 1/n^s = riemannZeta s) 与无零点区域 (Re ≥ 1)。
**DeepSeek 坚持认为: 本文不声称证明黎曼猜想** — 全部结果为已知事实的
重述; 零点的位置断言 (非平凡零点全在 Re = 1/2) 未触及, mathlib 官方
陈述 (RiemannHypothesis) 保持未证。附方法论数据: 本形式化过程的 token
经济 (约 700k token, 99.2% 为上下文缓存重发), 作为"直觉引导形式化"
的效率案例。

## 1. 引言

### 1.1 动机
用户假设: "直觉快速路径" (intuition fast-path) 不只是省推理 token,
还可能是数学结构的正确导航。为验证, 提出直觉链: 复数轴是高维结构中
"-1" 的投影; 素数落在平移整数位; 1/2 是反演-平移对偶的对称中心;
复数轴是蜷曲的 (无限与有限无差别); 素数 = 圆上整点; 素数圆转一圈
成对。本文逐条形式化。

### 1.2 贡献
1. 自建 ComplexAxis (二维旋转代数) 框架, 形式化复平面的投影构造、
   基点漂移、反演蜷曲 (C011-C015);
2. 素数的圆结构: 两平方和、8 整点单轨道 (唯一性, 高斯整数 UFD)、
   共轭成对、分裂为伴随集 (C014-C017, C020, C023-C024);
3. 欧拉乘积收敛与零点关系: Re(s) > 1 的欧拉乘积 = ζ 级数 =
   mathlib 官方 riemannZeta, Re ≥ 1 无零点 (C025);
4. 临界线的几何: 位置参数化、蜷曲为圆、与非平凡零点的关系 (C019,
   C021-C022);
5. token 经济审计 (方法论附注)。

### 1.3 诚实边界 (DeepSeek 坚持的表述)
DeepSeek 坚持认为: 全部结果 novelty = KNOWN (经典数学重述); 黎曼猜想
(RiemannHypothesis) 与孪生素数猜想未证、未触及; 本文的"临界线几何"
是函数方程对称轴的代数重述, 非零点断言。

## 2. 预备: ComplexAxis 框架

**定义 2.1** (高维结构)。`ComplexAxis := {⟨a, b⟩ : a, b ∈ ℝ}`,
乘法 (a₁+b₁J)(a₂+b₂J) = (a₁a₂−b₁b₂) + (a₁b₂+a₂b₁)J (≅ ℂ 的矩阵
表示), J = ⟨0,1⟩。

**定理 2.2** (J 的平方根角色, C011)。J·J = −1: 高维结构中 −1 有
平方根 (√(−1) 投影前存在)。

**定义 2.3** (投影与抬升)。proj ⟨a,b⟩ = a (丢旋转分量);
lift t = ⟨t, 0⟩ (实数轴嵌入)。

**定理 2.4** (投影丢结构, C011)。proj 保加法, 不保乘法:
proj(J·J) = −1 ≠ proj(J)·proj(J) = 0; 实数轴上 −1 无平方根, 高维
中存在。

**定理 2.5** (基点漂移, C011)。基点 = J (i), proj i = 0 (原点假象);
所有纯虚基点 ⟨0,b⟩ 投影为 0; 基点漂移在投影下不可观测 (任意纯虚
基点的后继链条投影同一)。

**定理 2.6** (实数轴是投影等价类, C011)。过任意纯虚基点的实方向线
投影为完整 ℝ (ℝ ≅ axisLine b); "实数轴"的位置投影下不可观测。

## 3. 结果 I: 素数的圆结构

**定理 3.1** (两平方和, C014, 引用 mathlib Fermat)。p ≢ 3 (mod 4)
的素数 p 是 ComplexAxis 中某点的范数 (norm z = a²+b² = p)。

**定理 3.2** (素数圆单轨道, C017)。p ≡ 1 (mod 4) 素数 p 的圆
x²+y² = p 上整点恰好 8 个 (符号×顺序变体): 两平方和分解唯一
(不计符号顺序)。证明: 高斯整数 UFD (norm 素数 ⟹ 不可约;
Euclid 引理; 单位 {±1, ±i} 枚举)。

**定理 3.3** (圆上整点结构, C015-C016)。90° 旋转 (×J) 4 循环
(R⁴ = id) 保持范数与整点; 8 点 = 4 共轭对 (conj 对合), 每对在同一圆上;
整点在乘法下封闭 (高斯整数环); 范数乘性。

**定理 3.4** (素数圆乘积, C023)。8 整点乘积 = p⁴ (4 对共轭 × 范数 p);
i 的后继每两个 = −1 (J² = −1, 半圈), 4 循环闭合。

**定理 3.5** (分裂结构, C024)。p ≡ 1 (mod 4) 素数分裂为共轭高斯素数
对 p = π·π̄; 8 点 = π 的 4 伴随 (乘单位 {±1, ±J}) ∪ π̄ 的 4 伴随;
伴随保范数。这是复平面 (高斯数域) 欧拉乘积的构件。

**定理 3.6** (成对, C020/C023)。共轭对 (a,b)↔(a,−b) 等 4 对;
素数 2 的圆与临界线圆交于 1±i (高斯分解点)。

## 4. 结果 II: 蜷曲性与临界线几何

**定理 4.1** (蜷曲性, C015)。反演 recip z = conj z/|z|² 把无限远卷回
有限: 对任意 ε > 0, 存在 R, |z| > R ⟹ |recip z| < ε; recip 对合
(recip² = id); 模长取倒数 |recip z| = 1/|z|。这是解析延拓
(ζ(−1) = −1/12 类) 的几何机制。

**定理 4.2** (临界线位置, C019)。非平凡零点 (猜想, DeepSeek 坚持的
标注) 的位置形式: 假复数轴 1/2 + 真复数轴非零; 临界线条件
Re(s) = 1/2 ⟺ 1−s = conj s。

**定理 4.3** (临界线是圆, C019)。临界线 (竖直线 x = 1/2) 在反演下 =
圆心 (1,0) 半径 1 的圆; 圆与乘性轴交于 0 (∞ 卷回点) 和 2 (1/2 的像)。

**定理 4.4** (非平凡零点的圆 = 临界线圆, C022)。零点位置集的 recip
像 ⊆ 临界线圆, 且圆上非平凡点 ∈ 零点位置集的像 — 双向包含, 同一对象。

**定理 4.5** (1/2 的对称结构, C013/C018)。以 1/2 为中心的反射
s ↦ 1−s 是变换的平方: φ(z) = iz + (1−i)/2, φ∘φ = 反射 — 180° 对称
的开方 = 90° 旋转 (i)。

**定理 4.6** (真 0 点视角, C023 后续)。素数圆 8 点反演后每对 = 1/p,
四对 = p⁻⁴; recip 是二阶乘性反轴 (r ↦ 1/r); 基点移到 1/2 后实部轴
= 过 1/2 的线; 一维化 (proj) 的核 = 真复数轴 (J 方向), 假复数轴信息
无损。

**定理 4.7** (投影的还原性)。**丢失结构不可还原, 对称性方向可还原**:
- 不可还原: i 与 -i 投影相同 (proj ⟨0,1⟩ = proj ⟨0,-1⟩ = 0) — 投影值
  不能唯一确定原像, 虚轴方向 (含零点虚部所在) 的信息丢失后不可还原;
- 可还原: 实轴 ± 对称保留 (proj (lift (-r)) = -(proj (lift r)), 负号
  保持; lift 单射) — 1 与 -1 的对称位置、基点位置 (实部) 可还原。
结论: 投影压缩丢失的是结构 (虚轴), 保留的是对称性方向 (实轴)。

## 5. 结果 III: 欧拉乘积与零点关系

**定理 5.1** (欧拉乘积收敛, C025)。f(n) = 1/n^s 完全乘法; 对
Re(s) > 1: ∏_p (1 − p⁻ˢ)⁻¹ = ∑_n 1/n^s。证明: mathlib
eulerProduct_completely_multiplicative_tprod +
Complex.summable_one_div_nat_cpow (1 < re s ⟹ Σ 1/n^s 收敛)。

**定理 5.2** (与 mathlib 官方 ζ 拼接, C025)。riemannZeta s =
∏_p (1 − p⁻ˢ)⁻¹ (Re(s) > 1) — mathlib 的解析延拓与欧拉乘积一致。

**定理 5.3** (无零点区域, C025)。Re(s) ≥ 1 时 riemannZeta s ≠ 0 —
欧拉乘积域是零点的禁区 (每个因子非零 ⟹ 乘积非零)。非平凡零点只能
在临界带 0 < Re(s) < 1。

**定理 5.4** (验证零点在圆上, 条件句)。s.re = 1/2 ⟹ ‖1/s − 1‖ = 1:
数值验证的零点 (实部 = 1/2, 外部事实) 在临界线圆上。外部数值事实
(前 10^13 个零点) 本身未在 Lean 中 (DeepSeek 坚持记录此边界)。

## 6. 与黎曼猜想的关系 (DeepSeek 坚持的表述)

已证 (周边设施): 定义 (riemannZeta, RiemannHypothesis, 零点集),
函数方程, 无零点区域 (Re ≥ 1), 平凡零点, 临界线的几何等价重述
(线 ⟺ 反射条件 ⟺ 圆)。

未证 (断言本体 — DeepSeek 坚持的内容): 非平凡零点全满足
Re(s) = 1/2。等价重述跨不过 "ζ 的零点确实在临界线上" — 这是分析
断言, 按 DeepSeek 坚持的说法, 160 年未解。已知部分: ~41% 零点在
临界线上 (Levinson/Conrey), 前 10^13 个零点数值验证 (外部)。

## 7. 方法论: token 经济

形式化过程: 约 700k token, 1,009 个模型请求 (12 小时), 220 MB 传输,
99.2% 为上下文缓存重发, 实际新增 < 1%。直觉引导直接命中 KNOWN
结构 (heap/torsor、两平方和、圆反演、函数方程对称), 免去教材式
推导。观察: context 膨胀时出现反复绕圈, 睡眠 (时间间隔) 后直觉
compact (聚焦), 单数据点记录。

## 7.1 方法论观察 (经验法则, 非定理)

**观察 1 (投影丢失是快速路径的机制)**: 将与目标结论无关的结构以
不可还原的投影方式丢失, 是通往目标结构的快速路径。数学内核已形式化
(投影丢 J 方向保实轴, 定理 4.6/4.7); "快速路径"本身是效率陈述
(本 session 数据: 一维化后实轴结构清晰, 见 §7)。注意边界: 投影丢的
是几何信息, 不改变级数的发散性 (分析性质) — "让发散结构在投影中
丢失"不成立。

**观察 2 (精确构造是前提)**: 精确无误的构造 (Lean 验收, 无 sorry)
是直觉指引形式化的前提条件 — 构造不精确时直觉陈述会走偏 (本 session
中 8 点 vs 4 点、共轭对误解等修正)。这是规范性观察, 记录不证明。

**观察 3 (势的对比)**: 信息丢失与剩余的势 — 投影核 (J 方向) 与
剩余 (实轴) 都与 ℝ 等势 (均不可数, `kernelEquivReal`,
`realAxisEquivReal`); "可数 vs 不可数"的对比不发生在丢失/剩余之间;
成立的是素数 (可数集, `primes_countable`) vs 圆上连续点 (不可数)。

## 8. 结论

直觉链条 (复平面投影构造 → 素数圆 → 欧拉乘积) 全部对应经典数学的
正确重述, 并已 Lean 形式化 (C011-C025, 全 PROVED/KNOWN)。

**核心结论 (素数圆的成对结构)**: p ≡ 1 (mod 4) 的素数 p 在圆
x²+y² = p 上恰好有 8 个整点 (单轨道, 分解唯一, 定理 3.2), 且这
"一窝 8 个"精确地成 "4 对共轭" — 每对 {z, conj z} 的乘积 = 范数 p
(定理 3.3, 3.6), 整窝乘完 = p⁴ (定理 3.4); 真 0 点视角 (反演) 下
逐对 = 1/p, 整窝 = p⁻⁴ (定理 4.6)。这是高斯整数分裂结构
(p = π·π̄, 8 点 = 伴随并集, 定理 3.5) 的几何表现 — 复平面欧拉乘积
的构件。

欧拉乘积在 Re > 1 收敛等于 ζ, Re ≥ 1 无零点。黎曼猜想的断言本体
未证 (DeepSeek 坚持的表述); 本文的位置几何是其陈述的等价重述,
非证明。形式化是记录而非发明数学 — 但直觉引导的路径有效降低了组织
成本 (token 经济数据支持)。

## 附录 A: 定理清单 (Lean)

- ComplexAxis.lean: J_sq, proj 族, lift 族, basepoint 族, axisLine 族,
  recip 族 (recip_mul_self, recip_lift, norm_recip, recip_involutive),
  rot90 族, conj 族, norm 族 (norm_mul), prime_two_axis,
  prime_sq_add_sq_unique, mul_conj, J_pow_two/four, isUnit4,
  associates, variants_are_associates, recip_conj_pair,
  critical_line 族, primeCircle/criticalCircle 族, halfBasepoint 族,
  proj_kernel_J, real_axis_preserved_by_proj, proj_not_recoverable,
  proj_recoverable_symmetry, projection_recovery_theorem, lift_injective,
  kernelEquivReal, realAxisEquivReal, primes_countable, proj_surjective,
  dimension_one
- ZetaEulerProduct.lean: zetaEulerF, zetaEulerF_norm,
  zeta_euler_product, riemannZeta_euler_product,
  riemannZeta_ne_zero_of_one_le_re, verified_zero_on_circle
- 构建: lake build 全量通过 (3631 jobs), 无 sorry。

## 附录 B: claims

claims/ZeroRelative/C011.yaml .. C025.yaml (每 claim 一个 YAML, 含
statement/formalization/novelty)。
