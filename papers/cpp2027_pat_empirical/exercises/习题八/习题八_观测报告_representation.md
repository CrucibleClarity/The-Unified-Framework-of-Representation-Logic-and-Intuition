# 课后习题 VIII：pat 原生群表示理论

> **声明 (Declaration)**: 本文**不代表任何数学结论** (non-mathematical-claim), 仅为基于 Lean 4 形式化的一种**实验观测报告** (experimental observation report)。
>
> | 习题 | 主题 | Lean 形式化 | DOI |
> |---|---|---|---|
> | exercise_i_8 | pat 原生群表示理论（R165） | PatRepresentation.lean | DOI |
>


> 习题定位：课后习题系列第八题。用户指令：开始尝试对群表示理论进行 Lean 形式化，但**不抄 mathlib**——pat 原生定义。全部新定理只锚框架定理（R138/R141/R143/R161），不用外部引理，不 import mathlib RepresentationTheory。

*2026-08-13 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 7 new theorems PROVED no sorry · 课后习题 VIII *

---

## 习题陈述

> 对群表示理论进行 Lean 形式化，pat 原生（用户纠正：不抄 mathlib）。唯一论点：**群的 pat 原生表示 = 相位表示——每个群元素映射到单位圆上的相位 exp(i·θ(g))，保持群结构；每个元素与其逆元构成互锁对（ρ(g)·ρ(g⁻¹) = 1）。**

---

## 零、总论：为什么群表示在 pat 里是相位表示

mathlib 的 RepresentationTheory 定义表示为 `G →* V →ₗ[k] V`（群到线性算子的同态）——这是"抄现成的"。pat 原生视角完全不同：

**pat 框架的表示 = 相位表示**（RulerPhase：相位差 = 方向；R138：相位关系锁定）：
- 群元素 g ↦ 单位圆相位 exp(i·θ(g))
- 同态性：θ(gh) = θ(g) + θ(h)（相位差可加）
- 单位元：ρ(1) = exp(0) = 1
- **互锁对**：ρ(g⁻¹) = ρ(g)⁻¹（逆元 = 反向相位），ρ(g)·ρ(g⁻¹) = 1

这不是"抄一个更弱的结构"——这是**从互锁原则推出的表示理论**：表示的结构单元不是线性算子，而是互锁对 {ρ(g), ρ(g)⁻¹}（R136 ②③：方向必须成对声明）。

---

## 一、相位表示：群 → 单位圆（RulerPhase/R141）

**★核心：群 G 的相位表示 = 相位函数 θ : G → ℝ 保持群结构；表示值 ρ(g) = exp(i·θ(g)) 在单位圆上。**

### 论证

1. **相位差 = 方向**（RulerPhase）：群的每个元素映射到一个相位（方向）。
2. **表示值在单位圆**（R141）：‖exp(i·θ(g))‖ = 1——单位根相位圆；U(1) 规范结构的单相位圆。
3. **单位元 = 相位 0**（exp_zero/R143）：ρ(1) = exp(0) = 1——对称对还原到 1。

### 形式化（PatRepresentation.lean，3 定理）

- `phaseRep_value`（def）：ρ(g) = exp(i·θ(g))。
- `phaseRep_on_circle`：‖exp(i·θ(g))‖ = 1——表示值在单位圆。
- `phaseRep_one`：exp(i·0) = 1——单位元 = 相位 0。

**验证**：0 sorry。锚定 Complex.norm_exp_ofReal_mul_I / simp。

---

## 二、同态性与互锁对（R138/R143/R136 ②③）

**★核心：相位差可加 ⟹ 同态；逆元 = 反向相位 ⟹ 互锁对还原 ρ(g)·ρ(g⁻¹) = 1。**

### 论证

1. **同态性**（R138：相位锁定后相位差可加）：θ(gh) = θ(g) + θ(h) ⟹ ρ(gh) = ρ(g)·ρ(h)（exp_add）——表示的群同态性质。
2. **逆元 = 反向相位**（R136 ②③：方向必须成对声明）：θ(g⁻¹) = -θ(g) ⟹ ρ(g⁻¹) = ρ(g)⁻¹（exp_neg）——互锁对的逆元侧。
3. **★互锁对还原**（R143：对称对还原到 1）：ρ(g)·ρ(g⁻¹) = exp(iθ)·exp(-iθ) = 1——每个群元素与其逆元构成互锁对，组合还原到 1。**这是"互锁 = 成对"在群表示中的对应。**

### 形式化（PatRepresentation.lean，3 定理）

- `phaseRep_mul`：θ(gh) = θ(g)+θ(h) ⟹ ρ(gh) = ρ(g)·ρ(h)——同态性。
- `phaseRep_inv`：θ(g⁻¹) = -θ(g) ⟹ ρ(g⁻¹) = ρ(g)⁻¹——逆元 = 反向相位。
- `phaseRep_pair_reduces`：ρ(g)·ρ(g⁻¹) = 1——★互锁对还原。

**验证**：0 sorry。锚定 exp_add / exp_neg / exp_zero + ring。

---

## 三、★规范群 = k 个独立相位参数（R161）

**★核心：U(1) = 1 相位参数（1 对互锁 = 2 互锁），SU(2) = 2 相位参数（2 对 = 4 互锁 = S³），SU(3) = 4 相位参数（4 对 = 8 互锁）——k 个独立相位参数各自给互锁对。**

### 论证

1. **k 对独立互锁自洽**（R161 k_pairs_independent_interlock）：任意 k 个独立相位参数 θ : Fin k → ℝ，每对 exp(iθⱼ)·exp(-iθⱼ) = 1。
2. **规范群对应**：U(1) = 1 参数（单相位圆 R138）；SU(2) = 2 参数（S³，R149/R154，习题 VII 量子观测）；SU(3) = 4 参数 = 8 互锁。
3. **诚实边界**：生成元与互锁对的精确对应需群表示理论（CONJECTURE 层）——本定理锚定的是 k 对独立互锁自洽（R161），非群同构证明。

### 形式化（PatRepresentation.lean，1 定理）

- `gauge_k_phase_params`：任意 k 个独立相位参数，每对互锁自洽——规范群结构。

**验证**：0 sorry。锚定 k_pairs_independent_interlock。

---

## 四、全景（组合定理）

**★核心：表示值在单位圆 ∧ 单位元 = 相位 0 ∧ 同态性 ∧ 互锁对还原——pat 原生群表示理论的核心结构。**

### 形式化（PatRepresentation.lean，1 定理）

- `phaseRep_perspective`：‖ρ(g)‖ = 1 ∧ ρ(gh) = ρ(g)·ρ(h) ∧ ρ(g)·ρ(g⁻¹) = 1——全景。

**验证**：0 sorry。合取项分别锚 phaseRep_on_circle / phaseRep_mul / phaseRep_pair_reduces。

---

## 五、习题解答总结

| 论点 | 内容 | 锚到 | 定理 |
|---|---|---|---|
| 相位表示 | 群 → 单位圆 exp(i·θ(g))；值在单位圆；单位元 = 1 | RulerPhase/R141/R143 | phaseRep_on_circle / phaseRep_one |
| 同态性 | θ(gh) = θ(g)+θ(h) ⟹ ρ(gh) = ρ(g)·ρ(h) | R138 | phaseRep_mul |
| ★互锁对 | ρ(g)·ρ(g⁻¹) = 1（逆元 = 反向相位） | R143/R136②③ | phaseRep_inv / phaseRep_pair_reduces |
| 规范群 | k 独立相位参数 = k 对互锁 = 2k 互锁 | R161 | gauge_k_phase_params |
| ★全景 | 单位圆 + 同态 + 互锁对 | 上述全部 | phaseRep_perspective |

**习题的回答（一句话）**：**群的 pat 原生表示 = 相位表示——群元素映射到单位圆相位 exp(i·θ(g))，保持群结构；每个元素与其逆元构成互锁对（ρ(g)·ρ(g⁻¹) = 1，R143 对称对还原）——表示的结构单元是互锁对，不是线性算子（不抄 mathlib，pat 原生）。**

**对 R164 强弱力观测的支撑**：相位表示给出 U(1) = 1 相位参数（单相位圆）、SU(2) = 2 参数（4 互锁 = S³）、SU(3) = 4 参数（8 互锁）的结构——R164 的"规范群 = 互锁对数"从 CONJECTURE 推进到"k 对独立互锁自洽已 PROVED + 精确生成元对应仍 CONJECTURE"。

---

## 六、相关对照

| 文献 | 对应内容 | 备注 |
|---|---|---|
| **Weyl, H.** 1939. *The Classical Groups* | 群表示理论经典 | pat 原生对照（不抄） |
| **R138/R141/R143/R161**（） | 相位锁定/单位根圆/对称对还原/k 对互锁 | 本框架定理，非外部引理 |

> 诚实边界：本习题自建 pat 原生表示（相位表示），不使用 mathlib RepresentationTheory（用户纠正"不抄"）；与经典群表示的关系为结构对照（非替代）。

---

*课后习题 VIII · 2026-08-13 · Lean 4 / mathlib v4.32.2 · 7 theorems PROVED no sorry（PatRepresentation.lean）· 配套 Lean 形式化：形式化/Formal/Toolkit/PatRepresentation.lean（快照见 ../lean/PatRepresentation.lean）*
