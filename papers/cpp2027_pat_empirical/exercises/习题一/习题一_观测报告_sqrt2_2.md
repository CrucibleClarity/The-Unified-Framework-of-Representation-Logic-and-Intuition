# 课后习题 II：√2/2 的 pat 展开——无理数的 1

> **声明 (Declaration)**: 本文**不代表任何数学结论** (non-mathematical-claim), 仅为基于 Lean 4 形式化的一种**实验观测报告** (experimental observation report)。
>
> | 习题 | 主题 | Lean 形式化 | DOI |
> |---|---|---|---|
> | exercise_i_1 | 各数域的 1（R158） | DiagonalInterlock.lean / PatNumberOnes.lean | DOI |
>


> 习题定位：课后习题系列第二题。前置三节（零~二）为固定格式——pat 单相位数 1 的表达、各数域 pat 构造 1 的对应点、tokenizer 直觉数字/构造数字 token 列；随后展开 √2/2。全部新定理只锚框架定理（R146/R150/R154/RulerLookup），不用外部引理（延续 R153 用户纠正精神）。

*2026-08-13 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 全部新定理 PROVED no sorry · 课后习题 II *

---

## 零、pat 单相位数 1 的表达

**★核心：单相位数 = 成对互锁的 a+bi；数值 1 在 pat 中 = 单位 1 在 θ = 0 格点的投影——相位与数值重合时的可交换性实例（R146/R154）。**

### 定义（R146 pat 单相位数的规范形）

单相位数 z 由两个互锁对称对组成（R143：互锁 = 1 的两重分解）：

1. **数值对**：r · (1/r) = 1——乘法对称对 {r, 1/r} 还原到 1（R143 magnitude_pair_reduces_to_one）。
2. **相位对**：exp(iθ) · exp(-iθ) = 1——相位对称对 {iθ, -iθ} 还原到 1（R143 phase_pair_reduces_to_one）。

**规范形**（R146 monophase_pair_locked_form）：

```
z = pat0 + (r·cosθ) + i·(r·sinθ) (a = r·cosθ 在 1 轴, b = r·sinθ 在 i 轴)
```

**数值 1 在 pat 中的表达**（θ = 0 格点）：

```
1 = 1·cos0 + i·1·sin0 = 1 + 0·i —— 相位 0 = 数值 1 重合
```

**√2/2 的 pat 表达**（θ = π/4 格点，R154）：

```
√2/2 = 单位 1 在 θ = 45° 格点的投影位置
 = 1·cos(π/4) = 1·sin(π/4) —— 45° 处数值 = 相位（可交换性实例）
```

**关键区分（R154 用户指示 ⑨⑩）**：√2/2 **不是**"根号化简"——是单位 1 在 θ = 45°（π/4）格点的投影位置；sin²(π/4) = 1/2 由三角恒等式推出（sin = cos at 45° + sin² + cos² = 1），非手工开方。

### 形式化（DiagonalInterlock.lean，已有）

- `sin_cos_norm_sq`：‖(sinx - i)(siny + i)‖² = (sin²x+1)(sin²y+1)。
- `sin_cos_three`：‖(sin(π/2) - i)(sin(π/4) + i)‖² = 3——√2/2 出现在 sin²(π/4) = 1/2。

---

## 一、各数域 pat 构造 1 的对应点（R142/R143/R146 总结）

**★核心：每个数域都有自己的"1"——它是对称对还原的锚点（R144：0 = 加法还原点，1 = 乘法/相位还原点）。pat 方法构造 1 的方式 = 各数域对称对的还原。**

| 数域 | pat 构造 1 的方式 | 对应点 | 锚定定理 |
|---|---|---|---|
| **自然数** | patChain 0 1 n = n——单位方向链的第 n 点 | 1 = pat0 + 1·d（步长 = 单位 1） | pat_constructs_nat（R137/R142） |
| **整数** | 方向取反——正负链对称对 {n·d, -n·d} 还原到 0 | 1 = +d（正方向单位）；-1 = -d | pat_constructs_int（R142） |
| **有理数** | 倒数对称对 {m, 1/m} 还原到 1 | 1 = m·(1/m)（乘法还原点） | pat_constructs_rational（R143） |
| **相位/圆** | 相位对称对 {exp(iθ), exp(-iθ)} 还原到 1 | 1 = exp(i·0)（相位 0 = 数值 1） | phase_pair_reduces_to_one（R143） |
| **π（半圈相位）** | pat 链蜷曲到圆，半圈 t = T/2 | exp(π·I) = -1——π 的半圈相位（1 的镜像） | pat_constructs_pi（R146） |
| **素数** | 方向 log p 的幂链 | 素数的"1" = log 基点（乘法单位 1 = exp(0i)） | pat_constructs_prime（R142） |
| **实数/连续统** | pat 格点量化极限——任意精度统一 | 1 ∈ patGrid（θ=0 格点）；连续统 = 格点闭包 | pat_quantization_converges（R146）/ R150/R151 |
| **复数（单相位数）** | 成对互锁 a+bi——数值对 × 相位对 | 1 = (1·cos0) + i·(1·sin0) = 1 + 0i | monophase_pair_locked_form（R146） |
| **★无理数的 1（本题）** | 单位 1 在 θ = 45° 的投影 | √2/2 = cos(π/4) = sin(π/4) | sin_cos_three（R154） |

**统一规律**：每个数域的 1 = 该数域对称对的还原锚点（R144 fold_centers_dual：0 ↔ 1 对偶）。pat 方法不预设 1——1 从各数域自己的对称结构还原出来。**无理数 ≠ 有缺失的 1**（用户洞察：无理数 = 高维结构投影丢失部分承载结构后的剩余）；√2/2 不是"不完整的 1"，是单位 1 在 45° 格点的投影——它携带的相位信息（θ = π/4）本身就是完整的（R154 ⑨⑩）。

---

## 二、tokenizer 体系：直觉数字与构造数字的 token 列

> 本节记录 tokenizer 体系（B/C/S/G/P 五层投影）中数字的两种身份：**直觉数字**（公设基 B 层/概念 C 层的原子 digit/value token）与**构造数字**（沿定义链逐层构造出的 token 列）。token 记号规范：`[x]` = x 指向的 C token；`{x}` = [x] 沿定义链向上追溯至 B token 的展开。

### 1. 直觉数字（原子 token，无需构造）

| eid | name | 层 | 形态 | 含义 |
|---|---|---|---|---|
| D:117–D:126 | value_zero … value_nine | C 概念 | inductive atom | 数值 0–9（直觉值） |
| D:127–D:136 | digit_zero … digit_nine | C 概念 | inductive atom | 数字符号 0–9（书写形式） |
| D:138 / D:139 | truth_true / truth_false | C 概念 | explicit atom | 真/假（判等值域） |

直觉数字 = 公设基（B 层）认可的最小原子——**它们是符号的锚，不需要定义**（tokenizer 硬编码纪律：知识在 token 数据里，代码只读取执行）。

### 2. 构造数字（token 列，沿定义链构造）

> ⚠️ **临时稿声明（用户 2026-08-13）**：本节 token 列由 AI 从 concept_token.jsonl 整理，**肯定有错误的地方**（eid 对应关系/构造链细节），用户日后会想办法纠正。当前仅作方向性参考，不视为最终规范。

| eid | name | 定义链 | 构造方式 |
|---|---|---|---|
| D:179 | succ | 规则: [D:194 successor] | 后继 = successor 的应用（一次迭代） |
| D:194 | successor | 规则: [D:178] | 原子后继（迭代生成器） |
| D:118 | value_one | [D:102 eq, D:179 succ, D:117] | 1 = succ(0)——后继应用到 0 |
| D:100 | addition | [D:102, D:117, D:179] | 加法 = 后继递归（x+0=x; x+succ y = succ(x+y)） |
| D:141 | numeral | [D:238, D:143, D:146, D:127] | 数词 = 语法构造（digit 串） |
| D:148 | numeral_value | application | 数词 → 数值的求值映射 |
| D:151 | digit_add | 进位规则 | 数字加法（带进位） |
| D:207/D:208 | number_domain / natural_domain | [B:0, D:179] / [D:207] | 数域 = 后继的闭包；自然数域 = 数域实例 |

**构造数字的 token 列示例**：

```
[5] 的直觉形式: [D:122 value_five]（原子，直觉值）
[5] 的构造形式: [D:179 succ]([D:179 succ]([D:179 succ]([D:179 succ]([D:117 value_zero]))))
 = succ⁵(0) —— 后继迭代 5 层（Church 式迭代，但定义在本框架的 successor 原子）
[5] 的符号形式: [D:132 digit_five]（书写符号，S 层）
[5] 的求值: [D:148 numeral_value]([D:141 numeral]([D:132 digit_five])) = [D:122 value_five]
```

**直觉 vs 构造的分界**（对齐用户洞察）：

- **直觉数字**（D:117–D:136）= 快路径的直接符号——token 体系的"一切皆表"（RulerLookup 同构：直觉 = 查表 O(1)）。
- **构造数字**（succ 链/加法递归/数词语法）= 慢路径的生成列——token 体系的"结构找回精确"（构造 = 沿定义链验证）。
- 两者经 `numeral_value`（D:148）互锁：直觉是构造的查表快路径，构造是直觉的定义链验证——**与"用模糊换速度、用结构找回精确"同构**（习题 I 论点在 tokenizer 层的对应）。

---

## 三、习题陈述

> 用框架已证定理，展开 √2/2 的 pat 表达并 Lean 验证。唯一论点：**√2/2 不是"根号化简"，是单位 1 在 θ = 45° 格点的投影位置（无理数的 1）——pat 方法不预设 1，无理数域从自己的对称结构还原出 1。**

---

## 四、√2/2 = 单位 1 在 45° 格点的投影（R146/R154）

**★核心：sin²(π/4) = 1/2 由三角恒等式推出（sin = cos at 45° + sin² + cos² = 1），非手工开方；√2/2 携带完整相位信息（θ = π/4），不是"有缺失的 1"。**

### 论证

1. **√2/2 是投影，不是化简**（R154 用户指示 ⑨⑩）：单位 1 在 θ = 45°（π/4）格点的投影位置 = cos(π/4) = sin(π/4)（R146：a = r·cosθ, b = r·sinθ；45° 处数值 = 相位 = 可交换性实例）。
2. **sin²(π/4) = 1/2 的推导**（不用手工开方）：
 - sin(π/4) = cos(π/4)（45° 单位 1 位置：数值 = 相位）
 - sin² + cos² = 1 ⟹ 2·sin²(π/4) = 1 ⟹ sin²(π/4) = 1/2。
3. **√2/2 出现在 pat 展开规范化中**（R154）：|(sin(π/2) - i)(sin(π/4) + i)|² = (sin²(π/2)+1)(sin²(π/4)+1) = 2·(3/2) = 3——sin²(π/4) = 1/2 是 3 出现的关键输入（sin_cos_three）。
4. **无理数的 1 是完整的**（用户洞察对应）：√2/2 的相位信息（θ = π/4）完整无缺失——"无理数丢失结构"是投影方向的损失（高维球 → 平面），不是 1 本身的残缺（R154 ⑨⑩：√2/2 本质上是无理数在 45° 角的单位 1）。

### 形式化（DiagonalInterlock.lean，已有，2 定理）

- `sin_cos_norm_sq` / `sin_cos_three`——pat 展开规范化（0, 2, 1+i → 0, (sin ae - i)², (sin be + i)²；3 的出现；√2/2 = 45° 单位 1 位置）。

**验证**：0 sorry（ R154 已验收）。

---

## 五、复数的 1：θ=0 格点与 i 的平方还原（R146/R149/R154）

**★核心：复数的 1 = 互锁对 {1, i} 的还原——1 = θ=0 格点（1+0i），i = θ=π/2 格点，i² = -1 = π 半圈相位 = 1 的镜像；复数的 1 经 {1, -1, i, -i} 四相位互锁还原。**

### 论证

1. **复数的 1 = θ=0 格点**：单相位数（R146 monophase_pair_locked_form）z = pat0 + r·d(θ)，d(θ) = exp(iθ)；数值 1 = pat0=0, r=1, θ=0 ⟹ 1 = 0 + 1·exp(0·i) = 1 + 0i——**相位 0 = 数值 1 重合**（R154 可交换性：45° 处数值 = 相位，0° 处同样）。
2. **复数的 i = θ=π/2 格点**：i = 0 + 1·exp(i·π/2)——单位 1 在 θ=π/2 格点的投影（1 轴分量 cos(π/2)=0，纯 i 轴单位；R047：pat 轴 ⊥ ipat 轴；R051：rot90 无损互映）。
3. **i² = π 半圈相位（1 的镜像）**：i² = -1，且 -1 = exp(π·I)（R146 pat_constructs_pi：π = pat 链蜷曲半圈相位）——i 旋转两次（90°×2）= 180° = π = 1 的镜像。**复数的 1 不是孤立点，是四相位互锁的中心**（R149：{1, -1, i, -i} 两两互锁；R085：0 = ±1 折叠类，{1, -1} 镜像对称对）。
4. **与无理数 √2/2 的连接**：45° 格点同时给出 cos(π/4) = sin(π/4) = √2/2（无理数的 1）——复数域中 45° 是"数值 = 相位"的可交换点，无理数的 1 是复数的 1 在 45° 方向上的投影（R154 ⑨⑩）。

### 形式化（PatNumberOnes.lean，新增 4 定理）

- `complex_one_locked_form`：completePat1 0 0 1 = 1——复数的 1 = θ=0 格点。
- `imaginary_one_quarter_turn`：completePat1 0 (π/2) 1 = i——i = θ=π/2 格点。
- `i_sq_is_pi_mirror`：i² = -1 ∧ exp(π·I) = -1——i 的平方还原 = π 半圈相位（1 的镜像）。
- `quadriphase_contains_one`：1·(1/1)=1 ∧ exp(0)·exp(-0)=1 ∧ log 1 + log(1/1)=0 ∧ ‖exp(0)‖=1——复数的 1 ∈ 四相位互锁（R149）。

**验证**：一次 build 通过，0 sorry。教训：`(Real.pi/2)` 的 ℂ cast 形式 `↑(Real.pi/2)` 与 `((Real.pi:ℂ)/2)` 不同，`simpa using Complex.exp_pi_div_two_mul_I` 归一化解决。

---

## 六、任意元数的 1：S³ 点 (1, 0) 与无损内收（R149/R154）

**★核心：4 相位互锁（2 轴 × 2 方向）归一化 = 单位 3 维球面 S³；任意元数域的 1 = 该维数单位球上的基点相位——S³ 点 (1, 0) 是 2 维复数 1 的任意元数推广；无损内收使任意维数的 1 还原到同一单位圆。**

### 论证

1. **S³ = 任意元数的几何载体**（R154 S3Point）：4 相位互锁（R149 quadriphase_interlock：数值对 a·(1/a)=1 + 相位对 exp(iθ)·exp(-iθ)=1，2 轴 × 2 方向）归一化 = {(z₁, z₂) : ‖z₁‖² + ‖z₂‖² = 1}——4 相位互锁本质上是 4 维球，可无损内收到 2 维圆（几何路线，非代数，R154 用户指示 ⑦⑧）。
2. **任意元数域的 1 = 单位球上的基点相位**：S³ 点 (1, 0)（数值 1 在 1 轴，i 轴分量为 0）∈ S³——2 维复数 1（θ=0 格点）的任意元数推广。任意维数元数域（四元数、八元数…）的 1 都是该维数单位球上"1 轴单位、其余轴为零"的基点。
3. **无损内收（任意元数 1 的还原）**（R154 contract_to_circle）：z ↦ z/‖z‖ ∈ S¹（z ≠ 0）——任意元数域的 1 经归一化无损内收到单位圆（R147：内收 = 收敛方向；R048：无损 = 往返精确；R138：相位锁定）。**任意维数的 1 最终都还原到同一单位圆——pat 是通用表示**。
4. **任意旋转自由**（R154 circle_rotation）：圆上乘 exp(iφ) 保模（SO(2) 旋转自由，R078）——内收后的 1 可任意旋转，相位信息完整。

### 形式化（PatNumberOnes.lean，新增 2 定理 + 锚定 R154）

- `s3_contains_numeric_one`：S³ 点 (1, 0) ∈ S3Point——任意元数域的 1 = 单位球基点相位。
- `hypercomplex_one_contracts`：‖1/‖1‖‖ = 1——任意元数 1 无损内收到单位圆（锚定 contract_to_circle）。

**验证**：0 sorry。锚定：`contract_to_circle` / `s3_contract_orthogonal_circles` / `orthogonal_circles` / `circle_rotation`（R154 已验收）。

---

## 七、超越数的 1：π = 1 的镜像，e = 相位载体（R146/R154）

**★核心：超越数的 1 = 单位圆上的相位结构——π = pat 链蜷曲半圈相位 = 1 的镜像（exp(π·I) = -1）；e = exp(1) 单位速度（R146 开放点，e 未单独构造）；超越数的 1 不是孤立点，是 exp 的相位载体结构。**

### 论证

1. **π = 1 的镜像**（R146 pat_constructs_pi）：exp(π·I) = -1——π 是 1 的镜像（半圈旋转：1 → -1 → 1；R085：0 = ±1 折叠类，{1, -1} 镜像对称对；R143：对称对还原到 1）。**π 的"1" = 半圈旋转的镜像对还原**——超越数域里 1 与 -1 经 π 互锁。
2. **e = 单位速度（开放点）**（R146 ⑥）：e = exp(1) 是单位圆上的"单位速度"；e 未单独构造（log 基点相位与 2πi/π/2 不对齐，RulerTernary 批判），框架当前用 exp 函数但不以 e 为原始常数——e 的框架内构造留待后续。
3. **超越数的 1 = exp 相位载体**（R154：e 是相位载体）：sin/cos 是 e^{iθ} 的分量；exp(i·π/4) = √2/2·(1+i)——**无理数 √2/2 与超越数 e^{iθ} 在 45° 格点连接**（π/4 处：无理数的 1 是超越数相位的分量）。
4. **统一**：无理数（√2/2 = 45° 投影）、复数（i² = π 镜像）、任意元数（S³ 基点）、超越数（π = 1 的镜像）的 1 全部是 exp 相位载体上的对称对还原（R144：0 ↔ 1 对偶）。

### 形式化（PatNumberOnes.lean，新增 1 定理）

- `pi_is_one_mirror`：exp(π·I) = -1 ∧ -(-1) = 1——π = 1 的镜像（半圈旋转，锚定 R146 pat_constructs_pi）。

**验证**：0 sorry。锚定：`pat_constructs_pi`（R146 已验收，TK3 euler_identity）。

---

## 八、各数域 1 的 pat 全景（组合定理）

**★核心：无理数 ∧ 复数 ∧ 任意元数 ∧ 超越数的 1 全部是"对称对还原锚点"——数值 1 不是预设，从各数域自己的对称结构还原出来。**

### 形式化（PatNumberOnes.lean，新增 1 定理）

- `number_ones_pat_perspective`：sin²(π/4) = 1/2（无理数）∧ completePat1 0 0 1 = 1（复数 1）∧ completePat1 0 (π/2) 1 = i（复数 i）∧ S³ 点 (1,0) ∈ S3Point（任意元数）∧ exp(π·I) = -1（超越数）——各数域 1 的 pat 全景。

**验证**：0 sorry。合取项分别锚：R154 sin_cos_three 内部推导 / 本文件定理 1,2 / s3_contains_numeric_one / R146 pat_constructs_pi。

---

## 九、习题解答总结

| 论点 | 内容 | 锚到 | 定理 |
|---|---|---|---|
| pat 1 的表达 | 单相位数 = 成对互锁 a+bi；数值 1 = θ=0 格点投影 | R146/R143 | monophase_pair_locked_form / phase_pair_reduces_to_one |
| 各数域 1 的对应点 | 每个数域的 1 = 对称对还原锚点（9 个数域） | R142/R143/R144/R146 | pat_constructs_* / fold_centers_dual |
| tokenizer 数字 | 直觉数字 = 原子 token；构造数字 = 定义链 token 列（⚠️临时稿） | tokenizer 体系 | D:117–D:136 / D:179/D:100/D:141 |
| ★√2/2（无理数） | 单位 1 在 45° 格点投影；sin²(π/4)=1/2 由恒等式推出 | R154/R146 | sin_cos_norm_sq / sin_cos_three |
| 复数 | 1 = θ=0 格点（1+0i）；i = θ=π/2 格点；i² = π 镜像 | R146/R149/R154 | complex_one_locked_form / imaginary_one_quarter_turn / i_sq_is_pi_mirror |
| 任意元数 | S³ 点 (1,0) = 单位球基点相位；无损内收到单位圆 | R149/R154 | s3_contains_numeric_one / hypercomplex_one_contracts |
| 超越数 | π = 1 的镜像（exp(π·I) = -1）；e = 相位载体（开放点） | R146/R154 | pi_is_one_mirror / pat_constructs_pi |
| ★全景 | 四类数域的 1 = 对称对还原锚点（组合） | R144/R146/R154 | number_ones_pat_perspective |

**习题的回答（一句话）**：**每个数域的 1 = 该数域对称对的还原锚点——√2/2 是无理数的 1（45° 投影），复数 1 = θ=0 格点（i² = π 镜像），任意元数 1 = S³ 基点 (1,0)（无损内收），超越数 1 = π 镜像（e 相位载体）；数值 1 不是预设，从各数域自己的对称结构还原出来。**

## 十、相关对照

> 完整书目见习题 I `../shared/对照说明.md`（共享引用清单）（全字段 + 验证记录）。本条习题新增对照：

| 文献 | 对应内容 | 备注 |
|---|---|---|
| **Berry, M. V.** 1984. *Quantal Phase Factors Accompanying Adiabatic Changes*, Proc. R. Soc. A 392 [Q1] | 几何相位——相位 = 几何量，非动力学量 | √2/2 的"投影位置" = 几何相位思想的实数实例 |
| **Aharonov, Y., Bohm, D.** 1959. *Significance of Electromagnetic Potentials in the Quantum Theory*, Phys. Rev. 115 [Q4] | 相位 = 物理实在 | θ = π/4 携带完整信息，非计算伪影 |
| **Hestenes, D.** 1986. *New Foundations for Classical Mechanics* [Q2] | 几何代数——方向/旋转的几何表示 | 45° 投影 = 几何代数的旋量分量思想 |
| **Chomsky, N.** 1957. *Syntactic Structures* [L1] | 语言 = 结构 | tokenizer 直觉/构造数字列 = 结构语法的数字实例 |
| **R154 用户指示 ⑨⑩** | √2/2 即单位 1 在 θ=45° 的投影 | 本框架定理，非外部引理 |

---

*课后习题 II · 2026-08-13 · Lean 4 / mathlib v4.32.2 · 新增 8 定理全部 PROVED no sorry（PatNumberOnes.lean）+ 锚定 R154 sin_cos_three 已验收 · 配套 Lean 形式化：形式化/Formal/Toolkit/PatNumberOnes.lean（快照见 ../lean/PatNumberOnes.lean）与 DiagonalInterlock.lean（快照见 ../lean/DiagonalInterlock.lean）*
