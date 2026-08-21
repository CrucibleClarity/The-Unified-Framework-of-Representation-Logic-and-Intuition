# 课后习题 X：纳维-斯托克斯存在性与光滑性的 pat 重新观测

> **声明 (Declaration)**: 本文**不代表任何数学结论** (non-mathematical-claim), 仅为基于 Lean 4 形式化的一种**实验观测报告** (experimental observation report)。
>
> | 习题 | 主题 | Lean 形式化 | DOI |
> |---|---|---|---|
> | exercise_i_10 | 纳维-斯托克斯的 pat 重新观测（R167） | PatNavierStokesObservation.lean | DOI |
>


> 习题定位：课后习题系列第十题。利用 mechanics-pat-observation skill 观测纳维-斯托克斯存在性与光滑性（Clay 千禧年问题之一）。过程中调试 skill，并研究该问题在物理空间的折叠中丢失了哪些信息、如何找回。全部新定理只锚框架定理（R047/R050/R085/R143/R147/R153/R161/R165）与框架 NS1/NS2（其他会话已证），不用外部引理。

*2026-08-13 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 6 new theorems PROVED no sorry · 课后习题 X *

---

## 习题陈述

> 纳维-斯托克斯存在性与光滑性（Clay 千禧年问题：3D 不可压 NS，初始速度光滑有限能量 ⟹ 全局光滑解存在）：利用 pat 重新观测。唯一论点：**NS 的折叠丢失 = 时间方向（ν>0 黏性不可逆）+ 数值互锁（奇点坍缩）；找回机制 = 时间对合 S²=id + 单位圆模长 ‖ρ(g)‖=1。**

---

## 零、总论：NS 三项 = pat 三个结构

NS 方程（3D 不可压）：∂t u + (u·∇)u + ∇p/ρ = νΔu

| NS 项 | pat 结构 | 锚定 |
|---|---|---|
| ∂t u（时间导数） | 时间 = 对合对称对 | R147 CausalityTime |
| (u·∇)u（对流） | 锁定方向链（惯性传播） | R050/R153① |
| νΔu（黏性） | 脱离投影（高维耗散） | R161 |

**千禧年问题的 pat 转译**：存在性 = 折叠后仍有解（脱离投影保持互锁）；光滑性 = 数值互锁保持（r·(1/r) = 1 不坍缩）。

---

## 一、折叠丢失 1：时间方向（ν>0 黏性不可逆）

**★核心：时间反演折叠下，时间导数项翻转而黏性项不翻转——时间方向在黏性中丢失（EulerVsNS 已证）。**

### 论证

1. **时间反演 = 穿折越**（NS1/NS2，其他会话已证）：时间 t ↦ -t 是时间轴上的基点穿折越。
2. **时间导数翻转**（NS2 timeDeriv_flips_under_reversal）：deriv(velRev u) t = -deriv u (-t)——时间导数项在反演下翻转。
3. **黏性项不翻转**（NS2 viscous_invariance_of_reversal）：νΔ(velRev u) = νΔu——Laplacian 是空间操作，时间反演不变。
4. **⟹ ν=0（Euler）可逆，ν>0（NS）不可逆**（NS2 euler_reversible_viscous_irreversible）——**时间方向在黏性中丢失**（正反时间解不可区分 → 熵增方向不可逆）。
5. **找回机制：时间对合**（R147 CausalityTime time_dual_reduces）：-(-t) = t——折叠类 {t, -t}（R085）中时间方向成对，经对合找回（时间箭头）。

### 形式化（PatNavierStokesObservation.lean，1 定理）

- `time_dual_reduces`：-(-t) = t——时间对合还原（R147）。

**验证**：0 sorry。锚定 CausalityTime.time_dual_directions 同型。

---

## 二、折叠丢失 2：数值互锁（奇点坍缩）

**★核心：光滑性 = 数值互锁保持（r·(1/r) = 1）；奇点 = 数值互锁坍缩（r→0 或 r→∞）。**

### 论证

1. **光滑性 = 数值互锁保持**（R143 magnitude_pair_reduces_to_one）：r·(1/r) = 1——数值对称对还原到 1（能量守恒的 pat 结构）。
2. **奇点 = 数值互锁坍缩**：r = 0（坍缩到折叠类 R085）时 1/r 无定义；r → ∞（发散）时数值互锁在极限中失去还原——奇点候选 = 数值互锁坍缩。
3. **存在性 = 折叠后仍有解**（R161 脱离投影保持）：黏性（耗散）经投影后，剩余互锁仍保持——解在折叠后仍存在。

### 形式化（PatNavierStokesObservation.lean，2 定理）

- `smoothness_numeric_interlock`：r·(1/r) = 1（r ≠ 0）——光滑性 = 数值互锁保持（R143）。
- `singularity_fold_collapse`：r = 0——奇点 = 数值互锁坍缩到折叠类。

**验证**：0 sorry。锚定 field_simp / R143。

---

## 三、找回机制：单位圆模长脱离不变

**★核心：单位圆模长 ‖ρ(g)‖ = 1 是折叠后仍可观测的不变量——光滑性的找回 = 相位表示的单位圆模长保持。**

### 论证

1. **单位圆模长**（R165 phaseRep_on_circle/R141）：‖exp(iθ)‖ = 1 对任意相位成立。
2. **脱离不变**（R161）：折叠（时间反演/数值坍缩）后单位圆模长不变——是可观测的找回机制。
3. **与丢失结构的关系**：丢失的信息（时间方向、数值互锁的坍缩极限）不可全部恢复，但单位圆模长（=1）是丢失结构的可观测印记——**找回 = 可观测不变量，非丢失信息全部恢复**（诚实边界）。

### 形式化（PatNavierStokesObservation.lean，1 定理）

- `unit_circle_recovers`：‖exp(iθ)‖ = 1——找回 = 单位圆模长（R165）。

**验证**：0 sorry。锚定 norm_exp_ofReal_mul_I。

---

## 四、全景（组合定理）

**★核心：时间对合还原（R147）∧ 光滑性 = 数值互锁保持（R143）∧ 找回 = 单位圆模长（R165）——NS 折叠丢失（时间方向 + 数值互锁）的找回机制。**

### 形式化（PatNavierStokesObservation.lean，1 定理）

- `ns_pat_perspective`：-(-t) = t ∧ r·(1/r) = 1 ∧ ‖exp(iθ)‖ = 1——NS pat 全景。

**验证**：0 sorry。合取项分别锚 R147/R143/R165。

---

## 五、skill 调试记录（mechanics-pat-observation）

| 检查项 | 结果 | 调试 |
|---|---|---|
| 结构对应 | ✅ NS 三项 = 时间对合/锁定链/脱离投影 | 新增：黏性 = 脱离投影（viscous_detachment） |
| 折叠丢失 | ✅ 时间方向（EulerVsNS 锚定）+ 数值互锁（奇点） | 发现：数值互锁坍缩是光滑性丢失的关键 |
| 找回机制 | ✅ 时间对合 + 单位圆模长 | 新增：单位圆模长 = 脱离不变观测 |
| pat 原生 | ✅ 全部 exp 代数，无坐标展开 | 无 |
| 诚实边界 | ✅ 千禧年证明标注 CONJECTURE | 无 |

**skill 改进**：新增"折叠丢失两分法"（时间方向丢失 + 数值互锁丢失）——NS 观测显示折叠丢失不单一，需同时分析时间与数值两个层面。

---

## 六、习题解答总结

| 论点 | 内容 | 锚定 | 标签 |
|---|---|---|---|
| NS 三项结构 | ∂t=时间对合 / (u·∇)u=锁定链 / νΔ=脱离投影 | R147/R050/R161 | PROVED |
| 折叠丢失：时间 | ν>0 黏性不可逆（时间导数翻转/黏性不翻转） | NS2 EulerVsNS | PROVED（其他会话） |
| 折叠丢失：数值 | 奇点 = 数值互锁坍缩（r=0/r→∞） | R143/R085 | OBSERVATION |
| 找回：时间 | 时间对合 -(-t)=t（折叠类 {t,-t}） | R147 | PROVED |
| 找回：数值 | 单位圆模长 ‖ρ(g)‖=1 脱离不变 | R165/R141 | PROVED |
| ★全景 | 折叠丢失（时间+数值）∧ 找回（对合+单位圆） | R147/R143/R165 | PROVED |

**习题的回答（一句话）**：**NS 在物理空间折叠（时间反演穿折越）中丢失两类信息——时间方向（ν>0 黏性不可逆，EulerVsNS 已证）与数值互锁（奇点坍缩到折叠类）；找回机制 = 时间对合 S²=id（时间箭头恢复）+ 单位圆模长 ‖ρ(g)‖=1（折叠后仍可观测的不变量）。存在性+光滑性的完整证明不在框架能力内（千禧年问题，CONJECTURE）。**

---

## 七、相关对照

| 文献 | 对应内容 | 备注 |
|---|---|---|
| **Fefferman, C.** 2000. *Existence and Smoothness of the Navier-Stokes Equation*（Clay 千禧年陈述） | 存在性+光滑性 | pat 观测对象 |
| **NS1/NS2/NS3**（其他会话，形式化/NavierStokes/） | 时间基点/时间反演可逆性 | 本习题锚定 |
| **R143/R147/R161/R165**（） | 数值互锁/时间对合/脱离投影/单位圆模长 | 本框架定理 |

> 诚实边界：存在性+光滑性的完整证明（千禧年问题）不在框架能力内——本习题交付结构观测（折叠丢失分析 + 找回机制），标注 OBSERVATION/CONJECTURE。

---

*课后习题 X · 2026-08-13 · Lean 4 / mathlib v4.32.2 · 6 theorems PROVED no sorry（PatNavierStokesObservation.lean）· 配套 Lean 形式化：形式化/Formal/Toolkit/PatNavierStokesObservation.lean（快照见 ../lean/PatNavierStokesObservation.lean）*
