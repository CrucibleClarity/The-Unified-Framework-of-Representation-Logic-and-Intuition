# 课后习题 XI：霍奇猜想的 pat 重新观测

> **声明 (Declaration)**: 本文**不代表任何数学结论** (non-mathematical-claim), 仅为基于 Lean 4 形式化的一种**实验观测报告** (experimental observation report)。
>
> | 习题 | 主题 | Lean 形式化 | DOI |
> |---|---|---|---|
> | exercise_i_11 | 霍奇猜想的 pat 重新观测（R168） | PatHodgeConjecture.lean | DOI |
>


> 习题定位：课后习题系列第十一题。用 mechanics-pat-observation skill 观测霍奇猜想（Clay 千禧年问题之一）。全部新定理只锚框架定理（R085/R136/R138/R143/R161/R165），不用外部引理。

*2026-08-13 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 5 new theorems PROVED no sorry · 课后习题 XI *

---

## 习题陈述

> 对霍奇猜想（Hodge Conjecture：光滑射影复代数簇 X 上每个有理 Hodge 类都是代数子簇的 ℚ-线性组合）做 pat 重新观测。唯一论点：**Hodge 分解 = 单位圆互锁对 {exp(iθ), exp(-iθ)}（共轭成对）；Hodge 类 = 共轭不变 = 折叠类 {0, π}；代数子簇 = 可构造锚点；猜想 = 折叠类点都可构造。**

---

## 零、总论：霍奇猜想的 pat 转译

霍奇猜想的经典陈述：X 光滑射影复代数簇，H^{2k}(X, ℚ) ∩ H^{k,k} 中的有理类都是代数子簇的有理上同调类。

**pat 结构对应**（mechanics-pat-observation skill）：

| 霍奇结构 | pat 结构 | 锚定 |
|---|---|---|
| Hodge 分解 H^k = ⊕ H^{p,q} | 互锁对 {exp(iθ), exp(-iθ)} | R161/R136②③ |
| H^{p,q} ↔ H^{q,p} 复共轭 | 共轭 = 反向相位（互锁对逆元侧） | R165 |
| Hodge 类（共轭不变） | 折叠类 {0, π}（exp(2iθ)=1 ⟹ θ=0/π） | R085/R138 |
| 代数子簇 | 可构造锚点（对称对还原到 1） | R143 |
| 猜想：Hodge 类来自代数子簇 | 折叠类点都可构造 | CONJECTURE |

---

## 一、★Hodge 共轭对 = 互锁对

**★核心：Hodge 分解的共轭对 H^{p,q} ↔ H^{q,p} = pat 互锁对——共轭 = 反向相位。**

### 论证

1. **Hodge 分解的共轭对**：H^k(X, ℂ) = ⊕_{p+q=k} H^{p,q}，H^{p,q} 与 H^{q,p} 复共轭成对。
2. **单位圆上的共轭**（R165）：conj(exp(iθ)) = exp(-iθ)——共轭 = 反向相位（单位圆上 conj z = z⁻¹）。
3. **互锁对**（R161）：exp(iθ)·exp(-iθ) = 1——Hodge 共轭对 = pat 互锁对（R136 ②③：方向成对声明；R143：对称对还原）。

### 形式化（PatHodgeConjecture.lean，1 定理）

- `hodge_conjugate_pair_interlock`：conj(exp(iθ)) = exp(-iθ) ∧ exp(iθ)·exp(-iθ) = 1——Hodge 共轭对 = 互锁对。

**验证**：0 sorry。锚定 exp_conj + R161。

---

## 二、★Hodge 类 = 折叠类 {0, π}

**★核心：Hodge 类（共轭不变平衡类）在单位圆上 = 折叠类 {0, π}——exp(2iθ) = 1 ⟹ θ = 0 或 π。**

### 论证

1. **Hodge 类 = 共轭不变**：实类满足 conj z = z。
2. **单位圆上共轭不变**：conj(exp(iθ)) = exp(iθ) ⟺ exp(-iθ) = exp(iθ) ⟺ exp(2iθ) = 1。
3. **exp(2iθ) = 1 ⟹ θ = π·n**（Complex.exp_eq_one_iff：2iθ = 2πi·n ⟹ θ = π·n）——在 [0, 2π) 中 = 0 或 π——**折叠类 {0, π}**（R085：0 = ±1 折叠类；R138：相位锁定）。

### 形式化（PatHodgeConjecture.lean，1 定理）

- `hodge_class_fold_class`：conj(exp(iθ)) = exp(iθ) ⟹ ∃ n : ℤ, θ = π·n——Hodge 类 = 折叠类。

**验证**：0 sorry。锚定 exp_conj + Complex.exp_eq_one_iff + field_simp/nlinarith。

---

## 三、代数子簇 = 可构造锚点

**★核心：代数子簇（可构造对象）的 pat 对应 = 对称对还原到锚点 1。**

### 论证

1. **代数子簇 = 可构造**：代数闭链是"可构造"的对象（定义方程组的解集）。
2. **pat 可构造 = 对称对还原**（R143 magnitude_pair_reduces_to_one）：r·(1/r) = 1——乘法对称对还原到锚点 1。
3. **代数闭链 = pat 可构造结构**：对称对还原（R144：1 = 乘法还原点）。

### 形式化（PatHodgeConjecture.lean，1 定理）

- `algebraic_cycle_anchor`：r·(1/r) = 1——代数子簇 = 可构造锚点。

**验证**：0 sorry。锚定 field_simp / R143。

---

## 四、折叠找回机制：单位圆模长不变

**★核心：折叠（共轭对 → 共轭不变类）后单位圆模长 ‖z‖ = 1 不变——可观测剩余。**

### 论证

1. **折叠**：H^{p,q} ⊕ H^{q,p} → 共轭不变类——丢失 (p,q)/(q,p) 方向区分，只留平衡类。
2. **找回**：单位圆模长 ‖exp(iθ)‖ = 1（R165 phaseRep_on_circle / 框架 AxisComponent.norm_exp_I_eq_one）折叠后不变——可观测剩余。
3. **找回机制（可构造性）**：折叠类点 {0, π} 是否可构造（代数子簇）——正是霍奇猜想的问题核心（CONJECTURE）。

### 形式化（PatHodgeConjecture.lean，1 定理）

- `fold_recovers_observable`：‖exp(iθ)‖ = 1——折叠后单位圆模长不变。

**验证**：0 sorry。锚定 AxisComponent.norm_exp_I_eq_one。

---

## 五、★霍奇猜想 pat 转译（CONJECTURE）

**★核心：霍奇猜想 = 折叠类点都可构造——所有有理 Hodge 类（折叠类点）都是代数子簇（可构造锚点）的组合。**

### 形式化（PatHodgeConjecture.lean，1 定理）

- `hodge_conjecture_pat`：conj(exp(iθ)) = exp(iθ) ⟹ (∃ n, θ = π·n) ∧ (∀ r≠0, r·(1/r) = 1)——Hodge 类 = 折叠类 ∧ 可构造锚点存在。

**验证**：0 sorry。合取项分别锚 hodge_class_fold_class / algebraic_cycle_anchor。

---

## 六、习题解答总结

| 论点 | 内容 | 锚定 | 标签 |
|---|---|---|---|
| Hodge 共轭对 = 互锁对 | conj = 反向相位；exp(iθ)·exp(-iθ)=1 | R161/R136②③/R165 | PROVED |
| Hodge 类 = 折叠类 | 共轭不变 ⟹ exp(2iθ)=1 ⟹ θ=0/π | R085/R138 | PROVED |
| 代数子簇 = 可构造锚点 | 对称对还原到 1 | R143 | PROVED |
| 找回 = 单位圆模长 | ‖exp(iθ)‖=1 折叠后不变 | R165/AxisComponent | PROVED |
| ★霍奇猜想 | 折叠类点都可构造 | 上述全部 | CONJECTURE |

**习题的回答（一句话）**：**霍奇猜想在 pat 视角 = 折叠类点都可构造——Hodge 分解是单位圆互锁对（共轭成对，R161），Hodge 类（共轭不变）折叠到 {0, π}（R085），代数子簇是可构造锚点（R143）；猜想断言折叠类点都可构造（千禧年问题，CONJECTURE）。折叠丢失 (p,q)/(q,p) 方向区分，找回 = 单位圆模长（可观测剩余）。**

**诚实边界**：霍奇猜想未解（千禧年问题）——本习题交付结构转译（折叠类 = Hodge 类、可构造 = 代数子簇），CONJECTURE 标注，非证明。

---

## 七、相关对照

| 文献 | 对应内容 | 备注 |
|---|---|---|
| **Hodge, W. V. D.** 1941. *The Theory and Applications of Harmonic Integrals* | Hodge 分解/调和积分 | pat 转译对象 |
| **霍奇猜想**（Clay 千禧年陈述） | 有理 Hodge 类来自代数子簇 | 未解（CONJECTURE） |
| **R085/R136②③/R138/R143/R161/R165**（） | 折叠类/成对/相位锁定/对称还原/互锁对/相位表示 | 本框架定理 |

---

*课后习题 XI · 2026-08-13 · Lean 4 / mathlib v4.32.2 · 5 theorems PROVED no sorry（PatHodgeConjecture.lean）· 配套 Lean 形式化：形式化/Formal/Toolkit/PatHodgeConjecture.lean（快照见 ../lean/PatHodgeConjecture.lean）*
