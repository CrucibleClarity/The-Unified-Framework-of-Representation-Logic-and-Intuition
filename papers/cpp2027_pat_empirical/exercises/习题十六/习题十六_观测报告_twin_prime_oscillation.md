# 课后习题 XVI：孪生素数间隔作为震荡周期轴


> 习题定位：课后习题系列第十六题。将孪生素数对的间隔 2 设置为震荡周期轴，把基点移动过去，观测震荡周期和对应发散轴的最长震荡距离。全部新定理只锚框架定理（R047/R142/R143/R159/R171/R172）+ mathlib 三角基础，不用外部引理。

*2026-08-13 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 6 new theorems PROVED no sorry · 课后习题 XVI *

---

## 习题陈述

> 将孪生素数对的距离（间隔 2）设置为一个震荡周期性的轴，然后把基点移动过去，观测震荡周期和对应发散轴的最长震荡距离。唯一论点：**间隔 2 = 震荡周期（exp(iπ(t+2)) = exp(iπt)）= 发散轴最长震荡距离（cos 投影从 +1 到 -1 = 2）——周期与最长距离自洽，间隔 2 是结构常数。**

---

## 零、总论：间隔 2 从"距离"升级为"震荡周期"

R172 把间隔 2 静态地对应到临界线圆直径 + 奇偶性折叠周期。本题把它**动态化**——间隔 2 是震荡轴（周期轴，R047）上的一个完整震荡周期：

```
震荡: osc(t) = exp(i·π·t) （周期轴上的震荡）
投影: 发散轴投影 = cos(π·t) （R047: 发散轴 = 实轴）
范围: 投影从 +1 (t=0) 到 -1 (t=1) （相位 0 = 数值 1, R143; 半圈）
最长距离: 1 - (-1) = 2 = 间隔 2 （★自洽）
```

**基点移动**（R142 基点漂移）：把基点从 0 移到震荡轴（t=1 中点，投影 -1），新基点下观测震荡——从新基点 -1 到远端 +1 的距离 = 2。

---

## 一、间隔 2 = 震荡周期（PROVED）

**★核心：震荡 osc(t) = exp(i·π·t) 的周期为 2——osc(t+2) = osc(t)。**

### 论证

1. **震荡定义**：osc(t) = exp(i·π·t)（相位角 π·t 随 t 线性增长）。
2. **周期 2**：osc(t+2) = exp(i·π·(t+2)) = exp(i·π·t)·exp(2πi) = exp(i·π·t)（exp(2πi) = 1，CompactToolkit.exp_two_pi_I_eq_one）——**间隔 2 = 震荡的一个完整周期**。
3. **与孪生素数连接**（R172）：孪生素数对 (p, p+2) 的间隔 2 = 震荡周期（R171 奇偶性折叠周期同型）。

### 形式化（PatTwinPrimeOscillation.lean，1 定理）

- `oscillation_period_two`：exp(i·π·(t+2)) = exp(i·π·t)——间隔 2 = 震荡周期。

**验证**：0 sorry。锚定 exp_add + CompactToolkit.exp_two_pi_I_eq_one。

---

## 二、震荡在发散轴的投影（PROVED）

**★核心：震荡 exp(i·π·t) 的实部（发散轴投影）= cos(π·t）；投影范围 [-1, 1]。**

### 论证

1. **发散轴投影**（R047：发散轴 = 实轴，周期轴 = 虚轴）：震荡的实部 = 发散轴投影 = cos(π·t)（Complex.exp_ofReal_mul_I_re）。
2. **投影范围**：cos(π·0) = 1（t=0，相位 0 = 数值 1，R143）；cos(π·1) = -1（t=1，半圈，Real.cos_pi）——发散轴投影范围 = [-1, 1]。

### 形式化（PatTwinPrimeOscillation.lean，2 定理）

- `oscillation_diverge_projection`：(exp(i·π·t)).re = cos(π·t)——震荡在发散轴投影。
- `oscillation_projection_range`：cos(π·0) = 1 ∧ cos(π·1) = -1——投影范围 [-1, 1]。

**验证**：0 sorry。锚定 Complex.exp_ofReal_mul_I_re / Real.cos_pi。

---

## 三、基点移动到震荡轴（PROVED）

**★核心：把基点从 0 移到震荡轴（t=1 中点，投影 -1）——新基点下观测震荡的相对范围。**

### 论证

1. **基点漂移**（R142/RulerDelta）：基点 = delta 的锚，值随基点漂移位置不变——把基点移到震荡轴中点（t=1，投影 -1）。
2. **新基点观测**：从新基点 -1 到远端 +1 的距离 = 2——观测结果与间隔 2 一致。

### 形式化（PatTwinPrimeOscillation.lean，1 定理）

- `basepoint_move_to_axis`：cos(π·1) = -1——基点移到震荡轴中点（t=1，投影 -1）。

**验证**：0 sorry。锚定 Real.cos_pi。

---

## 四、★最长震荡距离 = 2 = 间隔 2（PROVED）

**★核心：震荡在发散轴的投影从 +1 到 -1，最长震荡距离 = 1 - (-1) = 2——等于间隔 2 本身。周期与最长距离自洽。**

### 论证

1. **最长震荡距离**：投影范围 [-1, 1]——最长震荡距离 = 1 - (-1) = 2。
2. **★自洽**：震荡周期 = 2，发散轴最长震荡距离 = 2——**间隔 2 既是周期又是最长距离**（结构常数，R172：间隔 2 = 临界线圆直径 = 奇偶性周期）。

### 形式化（PatTwinPrimeOscillation.lean，1 定理）

- `max_oscillation_distance`：1 - (-1) = 2——★最长震荡距离 = 间隔 2。

**验证**：0 sorry。ring。

---

## 五、全景（组合定理）

**★核心：震荡周期 = 2（exp(iπ(t+2)) = exp(iπt)）∧ 发散轴投影范围 [-1,1]（cos(π·0)=1, cos(π·1)=-1）∧ 最长震荡距离 = 2 = 间隔 2——孪生素数间隔作为震荡周期轴：周期与最长距离自洽。**

### 形式化（PatTwinPrimeOscillation.lean，1 定理）

- `twin_prime_oscillation_perspective`：周期 2 ∧ 投影范围 [-1,1] ∧ 最长距离 2——全景。

**验证**：0 sorry。合取项分别锚 oscillation_period_two / oscillation_projection_range / max_oscillation_distance。

---

## 六、习题解答总结

| 论点 | 内容 | 锚定 | 标签 |
|---|---|---|---|
| 间隔 2 = 震荡周期 | exp(iπ(t+2)) = exp(iπt) | CompactToolkit/R171 | PROVED |
| 发散轴投影 = cos | (exp(iπt)).re = cos(πt) | R047 | PROVED |
| 投影范围 [-1,1] | cos(π·0)=1, cos(π·1)=-1 | R143/Real.cos_pi | PROVED |
| 基点移到震荡轴 | 新基点 = 震荡中点 -1 | R142 | PROVED |
| ★最长震荡距离 = 2 | 1-(-1) = 2 = 间隔 2 | R172 | PROVED |

**习题的回答（一句话）**：**孪生素数间隔 2 作为震荡周期轴——震荡 osc(t) = exp(iπt) 的周期是 2，发散轴投影 cos(πt) 从 +1 到 -1，最长震荡距离 = 1 - (-1) = 2 = 间隔 2 本身；基点移到震荡轴中点后观测，从新基点 -1 到远端 +1 仍是 2——震荡周期与发散轴最长距离自洽（间隔 2 是结构常数）。**

**诚实边界**：结构观测（震荡周期/投影范围/最长距离），非素数分布理论；间隔 2 的"自洽"是结构发现（周期 = 最长距离），非孪生素数无穷性断言。

---

## 七、相关对照

| 文献 | 对应内容 | 备注 |
|---|---|---|
| **R047**（） | 发散轴 ⊥ 周期轴 | 震荡轴结构基础 |
| **R142/R143**（） | 基点漂移 / 相位 0 = 数值 1 | 基点移动依据 |
| **R159/R171/R172**（） | 临界线圆 / 奇偶性周期 / 间隔 2 | 间隔 2 结构常数链 |

---

*课后习题 XVI · 2026-08-13 · Lean 4 / mathlib v4.32.2 · 6 theorems PROVED no sorry（PatTwinPrimeOscillation.lean）· 配套 Lean 形式化：形式化/Formal/Toolkit/PatTwinPrimeOscillation.lean（快照见 ../lean/PatTwinPrimeOscillation.lean）*
