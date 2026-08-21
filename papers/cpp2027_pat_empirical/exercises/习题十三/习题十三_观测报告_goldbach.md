# 课后习题 XIII：哥德巴赫猜想的 pat 重新观测

> **声明 (Declaration)**: 本文**不代表任何数学结论** (non-mathematical-claim), 仅为基于 Lean 4 形式化的一种**实验观测报告** (experimental observation report)。
>
> | 习题 | 主题 | Lean 形式化 | DOI |
> |---|---|---|---|
> | exercise_i_13 | 哥德巴赫猜想的 pat 重新观测（R170） | PatGoldbach.lean | DOI |
>


> 习题定位：课后习题系列第十三题。用 mechanics-pat-observation skill 观测哥德巴赫猜想（每个大于 2 的偶数是两个素数之和）。全部新定理只锚框架定理（R085/R128/R136②③/R143/R146/R159），不用外部引理。

*2026-08-13 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 6 new theorems PROVED no sorry · 课后习题 XIII *

---

## 习题陈述

> 对哥德巴赫猜想（Goldbach Conjecture：每个大于 2 的偶数 2n 都可表示为两个素数之和）做 pat 重新观测。唯一论点：**p + q = 2n ⟺ p, q 关于 n 对称（q = 2n - p）——哥德巴赫分解 = 素数对称对，关于偶数中心 n 折叠还原。**

---

## 零、总论：哥德巴赫 = 素数对称对

哥德巴赫猜想：2n = p + q（p, q 素数）。

**pat 结构对应**（mechanics-pat-observation skill）：

| 哥德巴赫结构 | pat 结构 | 锚定 |
|---|---|---|
| 2n = p + q | 对称对 {p, q} = {p, 2n-p} 关于 n | R085/R136②③ |
| p, q 关于 n 对称 | 镜像 S(x) = 2n - x（对合 S²=id） | R085/R128 |
| 偶数中心 n | 折叠中心（不动点 S(n) = n） | R085 |
| p, q 是素数 | 素数 = 方向 log p（单相位） | R159/R146 |
| ★猜想 | 每个偶数有素数对称对 | CONJECTURE |

---

## 一、p + q = 2n ⟺ 对称对

**★核心：哥德巴赫分解 2n = p + q 的代数等价 = q = 2n - p——p 和 q 关于偶数中心 n 对称。**

### 论证

1. **对称对**（R085 折叠类 / R136 ②③ 对称性成对声明）：p + q = 2n ⟺ q = 2n - p——{p, q} = {p, 2n-p} 关于 n 成对。
2. **哥德巴赫分解 = 对称对**：两个素数关于偶数中心对称分布。

### 形式化（PatGoldbach.lean，1 定理）

- `symmetric_pair_iff_sum`：p + q = 2n ⟺ q = 2n - p——哥德巴赫分解 = 对称对（linarith）。

**验证**：0 sorry。

---

## 二、镜像对合与中心不动点（R085/R128）

**★核心：偶数中心 n 的镜像 S(x) = 2n - x 是对合（S² = id），n 是不动点——折叠类还原。**

### 论证

1. **镜像对合**（R085/R128）：2n - (2n - x) = x——关于 n 的镜像 S² = id，素数对称对经两次镜像还原。
2. **中心不动点**（R085 折叠中心）：2n - n = n——偶数中心 n 是折叠中心，对称对关于 n 折叠，n 不变。

### 形式化（PatGoldbach.lean，2 定理）

- `mirror_involution`：2n - (2n - x) = x——镜像对合。
- `center_fixed`：2n - n = n——中心不动点。

**验证**：0 sorry。ring。

---

## 三、对称对的中点（R085/R143）

**★核心：p + q = 2n ⟺ q - n = -(p - n)——p 和 q 到中心 n 的距离相反（对称分布）。**

### 论证

1. **距离相反**：q - n = -(p - n)——p, q 到 n 等距反向（R085：0 = ±1 折叠类；R143：对称对还原到中心）。
2. **中点**：n 是 p, q 的中点——哥德巴赫分解 = 两个素数关于 n 对称。

### 形式化（PatGoldbach.lean，1 定理）

- `symmetric_pair_midpoint`：p + q = 2n ⟺ q - n = -(p - n)——对称对的中点（linarith）。

**验证**：0 sorry。

---

## 四、★哥德巴赫 = 素数对称对（CONJECTURE）

**★核心：哥德巴赫猜想断言每个偶数 2n 存在素数对称对 {p, q} 关于 n——两个素数方向在中心 n 折叠还原。**

### 论证

1. **素数 = 方向 log p**（R159 prime_log_monophase / R146）：哥德巴赫的两个素数是两个素数方向。
2. **★转译**：每个偶数 2n（n > 1）存在素数 p, q 满足 q = 2n - p——素数对称对关于中心 n 折叠还原（R085）。
3. **诚实边界**：强哥德巴赫未证（CONJECTURE；弱哥德巴赫已证，Helfgott 2013，外部文献）。

### 形式化（PatGoldbach.lean，1 定理）

- `goldbach_symmetric_decomposition`：p + q = 2n ⟺ q = 2n - p——哥德巴赫 = 素数对称对（代数部分 PROVED，存在性 CONJECTURE）。

**验证**：0 sorry。

---

## 五、全景（组合定理）

**★核心：对称对（p, q 关于 n）∧ 镜像对合（S²=id）∧ 中心不动点（S(n)=n）∧ 素数 = 方向 log p——哥德巴赫 = 素数对称对的折叠还原。**

### 形式化（PatGoldbach.lean，1 定理）

- `goldbach_pat_perspective`：对称对 ∧ 镜像对合 ∧ 中心不动点 ∧ 素数方向——全景。

**验证**：0 sorry。合取项分别锚 symmetric_pair_iff_sum / mirror_involution / center_fixed / R159。

---

## 六、习题解答总结

| 论点 | 内容 | 锚定 | 标签 |
|---|---|---|---|
| 对称对 | p + q = 2n ⟺ q = 2n - p | R085/R136②③ | PROVED |
| 镜像对合 | 2n - (2n - x) = x | R085/R128 | PROVED |
| 中心不动点 | 2n - n = n | R085 | PROVED |
| 对称中点 | q - n = -(p - n) | R085/R143 | PROVED |
| ★哥德巴赫 | 素数对称对存在性 | R159 + 上述 | CONJECTURE |

**习题的回答（一句话）**：**哥德巴赫猜想在 pat 视角 = 素数对称对——每个偶数 2n 的分解 p + q = 2n 等价于 p, q 关于中心 n 对称（q = 2n - p，镜像对合 S²=id，中心不动点）；两个素数 = 两个素数方向（log p，R159），在偶数中心 n 折叠还原。存在性未证（强哥德巴赫，CONJECTURE）。**

**诚实边界**：强哥德巴赫未证（CONJECTURE）——本习题交付结构转译（对称对 = 哥德巴赫分解的代数结构，PROVED；素数对称对存在性，CONJECTURE）。弱哥德巴赫（每个大于 5 的奇数是三个素数之和）已证（Helfgott 2013，外部文献，仅对照非证明）。

---

## 七、相关对照

| 文献 | 对应内容 | 备注 |
|---|---|---|
| **Goldbach, C.** 1742（给 Euler 的信） | 哥德巴赫猜想原始陈述 | pat 转译对象 |
| **Helfgott, H.** 2013. *Major arcs for Goldbach's theorem*（arXiv:1305.2897） | 弱哥德巴赫已证 | 仅对照，非证明 |
| **R085/R128/R136②③/R143/R146/R159**（） | 折叠类/镜像对合/成对/对称还原/素数方向 | 本框架定理 |

---

*课后习题 XIII · 2026-08-13 · Lean 4 / mathlib v4.32.2 · 6 theorems PROVED no sorry（PatGoldbach.lean）· 配套 Lean 形式化：形式化/Formal/Toolkit/PatGoldbach.lean（快照见 ../lean/PatGoldbach.lean）*
