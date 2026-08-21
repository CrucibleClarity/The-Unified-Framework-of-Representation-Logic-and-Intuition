# 课后习题 XIX：ABC 猜想的 pat 重新观测


> 习题定位：课后习题系列第十九题。ABC 猜想（Masser-Oesterlé 1985）的 pat 重新观测：rad(n) = 素因子折叠，ABC 猜想 = 加法被素因子折叠控制。全部新定理只锚框架定理（R085/R097/R144/R170），不用外部引理。

*2026-08-13 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 7 new theorems PROVED no sorry · 课后习题 XIX *

---

## 习题陈述

> ABC 猜想（经典）：任意 ε > 0，存在常数 K(ε)，对任意互素正整数 a, b, c 满足 a + b = c：c < K(ε)·rad(abc)^(1+ε)，其中 rad(n) = n 的无平方因子部分（互不相同素因子之积）。唯一论点：**rad(n) = 素因子折叠（素因子重数被折叠：p^k → p，R097 素数幂链单相位折叠重数到方向；R085 折叠类）；ABC 猜想 = 加法被素因子折叠控制——c（加法结果）的量级被 abc 的素因子折叠约束（R144 加法/乘法还原点对偶的边界断言）。**

---

## 零、总论：rad = 素因子折叠

rad(n) = n 的互不相同素因子之积（去掉重数）——这是 pat 的**素因子折叠**：

```
rad(12) = rad(2²·3) = 2·3 = 6 （重数 2 被折叠）
rad(2^k) = 2 （素数幂链折叠到方向）
```

**pat 含义**（R097 素数幂链单相位 + R085 折叠类）：素数幂链 p^k 在 log 视角是单相位 k·log p——rad 把重数 k（相位）折叠掉，保留素因子 p（方向）。**rad(n) = n 在素因子方向上的折叠像。**

---

## 一、rad 的性质（PROVED）

**★核心：rad(p^k) = p（幂链折叠到方向）；rad(n) | n（折叠像整除原数）；互素时 rad 可分配（无共享方向）；rad(1) = 1（空折叠）。**

### 论证

1. **rad(p^k) = p**（`rad_prime_pow`）：素数幂链 p^k 的素因子折叠 = p——重数 k 被折叠（丢指数，R085），素因子方向 p 保留（R097 单相位）。
2. **rad(n) | n**（`rad_dvd_self`）：折叠像整除原数——折叠只丢重数不丢方向（不增）。
3. **互素可分配**（`rad_coprime_mul`）：互素 a, b（无共享素因子方向）→ rad(a·b) = rad(a)·rad(b)——折叠对互素乘法可分配（折叠类互不重叠）。
4. **rad(1) = 1**（`rad_one`）：空折叠 = 乘法还原点 1（R144）。

### 形式化（PatAbcConjecture.lean，5 定理）

- `rad`：rad(n) = 素因子折叠（factorization.support 上的素数积）。
- `rad_prime_pow`：rad(p^k) = p——幂链折叠到方向。
- `rad_dvd_self`：rad(n) | n——折叠像整除原数。
- `rad_coprime_mul`：互素时 rad(a·b) = rad(a)·rad(b)——互素可分配。
- `rad_one`：rad(1) = 1——空折叠。

**验证**：0 sorry。锚定 mathlib factorization + R085/R097 精神。

---

## 二、abc 三元组 = 加法对称对还原（PROVED）

**★核心：a + b = c 是加法对称对还原（R144 加法还原点 0；R170 哥德巴赫对称对结构）。**

### 论证

1. c = a + b ⟺ a + b - c = 0——加法三元组还原到加法还原点 0（R144）。
2. R170 哥德巴赫对称对：c = a + b 是加法对称对还原。
3. 互素 = 无共享素因子 = 折叠类互不重叠。

### 形式化（PatAbcConjecture.lean，1 定理）

- `abc_add_reduce`：c = a + b → a + b - c = 0——加法对称对还原。

**验证**：0 sorry。ring。

---

## 三、★ABC 猜想 = 加法被素因子折叠控制（CONJECTURE）

**★核心：任意互素加法分解 a + b = c，加法的结果 c 被 abc 的素因子折叠（rad）控制：c < K(ε)·rad(abc)^(1+ε)。**

### 论证

1. **rad(abc) = abc 的素因子折叠**：互素时 rad(abc) = rad(a)·rad(b)·rad(c)（折叠类互不重叠，第一节可分配性）。
2. **猜想断言**：加法的量级 c 被乘法结构（素因子方向折叠）约束——R144 加法/乘法还原点对偶的边界断言。
3. **实例**：(1, 8, 9)：1+8 = 9，rad(72) = 6，c/rad = 1.5——强 ABC 实例（c > rad，但 c < rad^(1+ε) 对 ε > 0）。
4. **诚实边界**：猜想未证（CONJECTURE；望月新一 2012 IUT 声称证明，未被普遍接受——外部文献仅对照）。

### 形式化（PatAbcConjecture.lean，1 定理）

- `abc_pat_perspective`：rad(p²) = p ∧ rad(1) = 1 ∧ rad(2) | 2——全景（结构观测，非猜想证明）。

**验证**：0 sorry。合取项分别锚第一节定理。

---

## 四、习题解答总结

| 论点 | 内容 | 锚定 | 标签 |
|---|---|---|---|
| rad(p^k) = p | 素数幂链折叠到方向 | R097/R085 | PROVED |
| rad(n) \| n | 折叠像整除原数 | R085 | PROVED |
| 互素可分配 | rad(a·b) = rad(a)·rad(b) | R085 | PROVED |
| rad(1) = 1 | 空折叠 = 乘法还原点 | R144 | PROVED |
| abc = 加法还原 | a + b - c = 0 | R144/R170 | PROVED |
| ★猜想 = 加法被折叠控制 | c < K(ε)·rad(abc)^(1+ε) | — | CONJECTURE |

**习题的回答（一句话）**：**rad(n) = 素因子折叠（重数是相位被折叠，素因子是方向保留）；ABC 三元组 a + b = c 是加法对称对还原（R144/R170）；ABC 猜想 = 加法被素因子折叠控制——加法的结果 c 的量级不超过 abc 素因子折叠的 (1+ε) 次方（CONJECTURE，未证；望月新一 2012 IUT 声称证明，未被普遍接受，仅对照）。**

**诚实边界**：结构观测（rad 折叠性质、加法还原结构），非猜想证明；ABC 猜想本身未证（CONJECTURE）。

---

## 五、相关对照

| 文献 | 对应内容 | 备注 |
|---|---|---|
| **R097**（） | 素数幂链单相位（log 视角） | 幂链折叠到方向 |
| **R085**（） | 折叠类 | 折叠像 = 原数的因子 |
| **R144**（） | 加法还原点 0 / 乘法还原点 1 | abc 加法还原 + rad(1) |
| **R170**（） | 哥德巴赫对称对 | c = a + b 对称对还原 |

---

*课后习题 XIX · 2026-08-13 · Lean 4 / mathlib v4.32.2 · 7 theorems PROVED no sorry（PatAbcConjecture.lean）· 配套 Lean 形式化：形式化/Formal/Toolkit/PatAbcConjecture.lean（快照见 ../lean/PatAbcConjecture.lean）*
