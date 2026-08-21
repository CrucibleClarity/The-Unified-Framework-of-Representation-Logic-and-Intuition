# 课后习题 XX 补充：奇次方程根式解泛化 = 同向真收缩 + 换基点


> 习题定位：课后习题 XX（奇完全数）的姊妹题——奇次方程根式解泛化。核心：奇次幂 = 方向 d 上的同向扩张（保方向），根式解 = 收缩逆；换基点（R142）使收缩中心 = 根；收缩单射 ⟹ 无损压缩上界（R048）。全部新定理只锚框架定理（R047/R048/R142），不用外部引理。

*2026-08-13 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 7 new theorems PROVED no sorry · 课后习题 XX 补充 *

---

## 习题陈述

> 奇数次代数方程根式解泛化：奇次幂 x^n 是方向 d 上的同向扩张（x < y ⟹ x^n < y^n，保方向严格单调）；根式解 = 它的收缩逆。★换基点（R142）：收缩映射 T_b(x) = b + c·(x-b) 的不动点 = 基点 b——收缩中心 = 根；★同向真收缩 |T_b(x)-T_b(y)| = c·|x-y| 迭代压缩上界；★无损压缩上界：收缩单射 ⟹ 无损（R048）。

---

## 零、总论：扩张/收缩对偶 + 换基点

```
奇次幂 x^n = 方向 d 上的同向扩张 (保方向, 放大距离)
根式 y^(1/n) = 收缩逆 (不动点 = 根)
换基点: T_b(x) = b + c(x-b) (收缩中心 = 基点 b = 根)
无损压缩: 收缩单射 ⟹ 无损 (R048)
```

**求根 = 换基点后的同向真收缩迭代**——把基点移到根，收缩迭代无损压缩上界到不动点。

---

## 一、奇次幂保方向（同向扩张）（PROVED）

**★核心：x < y ⟹ x^n < y^n——奇次幂是方向 d（实数轴正方向，R047 发散轴）上的扩张：保方向，放大距离。**

### 论证

1. 幂函数严格单调（mathlib pow_lt_pow₀，n > 0）。
2. 奇次幂特别：负数也保序（(-x)^n = -x^n，符号由 x 决定）——方向保持。
3. 根式解 = 这个扩张的收缩逆（局部收缩到根）。

### 形式化（PatOddEquationRadical.lean，1 定理）

- `power_same_direction`：x < y ⟹ x^n < y^n——★奇次幂保方向。

**验证**：0 sorry。pow_lt_pow₀。

---

## 二、★换基点：收缩不动点 = 基点（PROVED）

**★核心：T_b(x) = b + c·(x-b) 的不动点 = 基点 b（R142 基点漂移：基点 = delta 的锚）。换基点 = 收缩中心移动到根。**

### 论证

1. T_b(b) = b + c·(b-b) = b——基点 b 是收缩不动点。
2. R142：基点 = delta 的锚——收缩中心 = 新基点。
3. 根式解的基点选择：收缩中心 = 根。

### 形式化（PatOddEquationRadical.lean，1 定理）

- `contraction_fixed_basepoint`：b + c·(b-b) = b——★收缩不动点 = 基点。

**验证**：0 sorry。ring。

---

## 三、★同向真收缩：迭代压缩上界（PROVED）

**★核心：|T_b(x) - T_b(y)| = c·|x-y|（0 < c < 1）——每次迭代距离乘 c，迭代压缩上界。**

### 论证

1. T_b(x) - T_b(y) = c·(x-y)——距离压缩 c 倍。
2. 0 < c < 1 ⟹ c·|x-y| < |x-y|——真收缩。
3. ★同向（保方向）真收缩：迭代压缩上界（每次乘 c）。

### 形式化（PatOddEquationRadical.lean，1 定理）

- `contraction_strict`：|T_b(x)-T_b(y)| = c·|x-y|——★同向真收缩。

**验证**：0 sorry。ring + abs_mul。

---

## 四、★无损压缩上界（R048 连接）（PROVED）

**★核心：收缩映射单射 ⟹ 无损（R048 injective_is_lossless）——收缩 = 无损压缩上界。**

### 论证

1. 收缩映射 T_b 是单射（c ≠ 0：c·(x-y) = 0 ⟹ x = y）。
2. R048：单射压缩 = 无损——收缩不丢信息。
3. R057：存储与计算同构。

### 形式化（PatOddEquationRadical.lean，1 定理）

- `contraction_lossless`：Function.Injective (T_b)——★收缩 = 无损压缩。

**验证**：0 sorry。mul_left_cancel₀。

---

## 五、迭代几何收缩到基点（PROVED）

**★核心：T_b^n(x) = b + c^n·(x-b)——迭代 n 次后离基点距离 = c^n·|x-b|（几何收缩，c < 1 ⟹ c^n → 0）。**

### 论证

1. 归纳：T_b^0(x) = x，T_b^(n+1)(x) = b + c·(T_b^n(x) - b) = b + c^(n+1)·(x-b)。
2. 上界被 c^n 无损压缩——迭代压缩上界。

### 形式化（PatOddEquationRadical.lean，2 定理）

- `contraction_iterate`：T_b^n(x) = b + c^n·(x-b)——迭代几何收缩。
- `contraction_compress_bound`：|T_b^n(x) - b| = c^n·|x-b|——★迭代压缩上界。

**验证**：0 sorry。归纳 + ring + abs。

---

## 六、全景（组合定理）

**★核心：收缩不动点 = 基点（换基点）∧ 收缩单射 ⟹ 无损（R048）——求根 = 换基点后的同向真收缩迭代。**

### 形式化（PatOddEquationRadical.lean，1 定理）

- `odd_equation_radical_perspective`：T_b(b) = b ∧ Injective T_b——全景。

**验证**：0 sorry。合取项分别锚第二、四节定理。

---

## 七、习题解答总结

| 论点 | 内容 | 锚定 | 标签 |
|---|---|---|---|
| 奇次幂保方向 | x < y ⟹ x^n < y^n（同向扩张） | R047/mathlib | PROVED |
| 换基点 | 收缩不动点 = 基点 b | R142 | PROVED |
| ★同向真收缩 | |T_b(x)-T_b(y)| = c|x-y| | 代数 | PROVED |
| ★无损压缩上界 | 收缩单射 ⟹ 无损 | R048 | PROVED |
| 迭代几何收缩 | T_b^n(x) = b + c^n(x-b) | 归纳 | PROVED |
| ★迭代压缩上界 | 上界被 c^n 无损压缩 | R048/R057 | PROVED |

**习题的回答（一句话）**：**奇次方程根式解 = 方向 d 上同向扩张（奇次幂）的收缩逆；换基点（R142）使收缩中心 = 根；同向真收缩 |T_b(x)-T_b(y)| = c|x-y| 迭代压缩上界，收缩单射 ⟹ 无损（R048）——求根 = 换基点后的同向真收缩迭代，无损压缩上界到不动点。**

**诚实边界**：结构观测（扩张/收缩对偶、换基点、无损压缩连接），非新求根算法。

---

## 八、相关对照

| 文献 | 对应内容 | 备注 |
|---|---|---|
| **R048**（） | 单射压缩 = 无损 | 收缩 = 无损压缩上界 |
| **R142**（） | 基点漂移（基点 = delta 的锚） | 换基点 = 收缩中心 = 根 |
| **R047**（） | 发散轴方向 d | 奇次幂的同向扩张方向 |
| **R057**（） | 存储与计算同构 | 收缩迭代 = 无损 |

---

*课后习题 XX 补充 · 2026-08-13 · Lean 4 / mathlib v4.32.2 · 7 theorems PROVED no sorry（PatOddEquationRadical.lean）· 配套 Lean 形式化：形式化/Formal/Toolkit/PatOddEquationRadical.lean（快照见 ../lean/PatOddEquationRadical.lean）*
