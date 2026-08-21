# 课后习题 Pat0-1：相位产生——相位从哪里来


> 习题定位：课后习题 Pat0 系列第一题。Pat 理论中相位（周期方向）不是公设，而是**对称性对的复合产物**——两个反射（对称性）复合产生旋转（相位生成元）。全部新定理锚定已验收定理（R047/R083/R085/R136/R138/R227/R228/R231）+ mathlib 实数基础，零单相位数依赖。

*2026-08-14 · Internal research exercise · Lean 4 / mathlib v4.32.2 · 5 new theorems PROVED no sorry · 课后习题 Pat0-1 *

---

## 习题陈述

> 回答 Pat 理论的开放问题：**相位（周期方向）从哪里来？** 唯一论点：**相位 = 对称性对的复合——实轴反射 S 与虚轴反射 Sv 的复合是旋转 J²（180°），旋转轨道即相位（J⁴ = id），相位轴是 S 的取反特征空间（虚轴），相位产生即升维（虚轴在实轴 proj = 0），相位锚定于互逆对和（折叠类 ±1）——相位不需要作为新公设。**

---

## 零、总论：相位从"公设的周期轴"升级为"对称性对的复合产物"

R047 把虚轴 J 作为周期轴（S 取反特征空间）；R083 把 S（周期 2）与 R（旋转）统一为自指迭代 T 家族。本题回答相位**从哪来**：

```
对称性 S (反射, 周期 2, R083)
 ↓ 反射对复合 (新: Sv∘S = J²)
旋转 J (相位生成元, 周期 4)
 ↓ J 迭代轨道 (R227: J⁴ = id)
相位 (周期结构)
 ↓ 特征空间 (R047: S 取反方向)
相位轴 = 虚轴 (实轴之外, proj = 0)
 ↓ 升维 (R231: 投影有损)
相位维度 (1 维 → 2 维)
 ↓ 锚定 (R136/R228: 互逆对和 = 0)
相位折叠类 (±1, R085)
```

**唯一论点**：相位不是公设，是**对称性对的复合产物**——两个反射复合产生旋转（相位生成元），相位轨道/特征空间/升维/锚定构成相位产生的完整链。

---

## 一、反射对复合 = 旋转（相位生成元）（PROVED）

**★核心：Sv∘S = J²——两个反射（对称性）的复合产生旋转（相位）。**

### 论证

1. **实轴反射**（R227）：S(x,y) = (x,-y)，det = -1，S² = id（周期 2，R083）。
2. **虚轴反射**（新定义）：Sv(x,y) = (-x,y)，det = -1。
3. **复合**：Sv(S(x,y)) = Sv(x,-y) = (-x,-y) = J(J(x,y))——180° 旋转 J²。

**含义**：单个反射是周期 2 的镜像（R083）；**反射对（对称性对）的复合产生旋转（相位生成元）**——相位不是原始对象，是对称性对的复合产物。T 家族（R083）内部，反射（周期 2）与旋转（周期 4）通过复合互相产生。

### 形式化（PhaseGeneration.lean，1 定理）

- `reflection_pair_composes_rotation`：Sv (S v) = J (J v)——反射对复合 = 旋转。

---

## 二、相位 = 旋转轨道（PROVED）

**★核心：相位是旋转生成元 J 的轨道——J⁴ = id（周期闭合）。**

### 论证

1. **旋转生成元**（R227）：J(x,y) = (-y,x)，90° 旋转。
2. **周期 4**（R227 rotation_period_four）：J(J(J(J v))) = v——90° × 4 = 360°，一圈闭合。
3. **相位 = 轨道**：相位是旋转轨道的周期性——相位是 J 迭代的周期结构。

### 形式化（PhaseGeneration.lean，1 定理）

- `rotation_pair_generates_period`：J⁴ = id——相位 = 旋转轨道。

---

## 三、相位轴 = S 取反特征空间（PROVED）

**★核心：相位轴（虚轴）是反射对称性 S 的取反方向——S(0,y) = -(0,y)。**

### 论证

1. **特征空间分解**（R047/R227）：发散轴（实轴，S 固定，特征值 +1）与周期轴（虚轴，S 取反，特征值 -1）是同一共轭对称性 S 的两个特征空间。
2. **相位轴 = 取反特征空间**：相位（周期）方向是 S 的取反方向——与发散轴共享同一对称性。

### 形式化（PhaseGeneration.lean，1 定理）

- `phase_axis_is_reflected_eigenspace`：S (imagAxis y) = -imagAxis y——相位轴 = S 取反特征空间。

---

## 四、相位产生 = 升维（PROVED）

**★核心：相位信息在实轴（发散轴）上不可观测——proj(imagAxis y) = 0，相位产生需要扩展维度。**

### 论证

1. **投影有损**（R231 proj_loses_imag）：虚轴（周期）整体投影为 0——降维丢周期。
2. **升维**：相位（周期信息）的产生需要实轴之外的维度——1 维（发散实轴）→ 2 维（复平面）。
3. **对称**（R231）：相位消失即降维；相位产生即升维——维度动力学与相位产生互逆。

### 形式化（PhaseGeneration.lean，1 定理）

- `phase_generation_expands_dimension`：proj (imagAxis y) = 0 ∧ (imagAxis y ≠ (0,0) ↔ y ≠ 0)——相位产生 = 升维。

---

## 五、相位锚定 = 互逆对和（PROVED）

**★核心：相位锚定于折叠类——互逆箭头对和 = 0（d + (-d) = 0）。**

### 论证

1. **互逆对和**（R136 declared_pair_anchors / R228）：d + (-d) = 0——互逆对锚定折叠类 0。
2. **折叠类**（R085）：0 = ±1 折叠类——相位锚定于折叠类。
3. **锁定后可加**（R138 locked_phase_relation_composes）：(θ₃-θ₂)+(θ₂-θ₁) = θ₃-θ₁——相位差锁定后良定义可加。

### 形式化（PhaseGeneration.lean，合成定理内）

- `phase_generation_synthesis` 第五段：∀ d, d + (-d) = 0——相位锚定。

---

## 六、核心合成：相位产生机制合一（PROVED）

**★核心：五段合一——相位 = 对称性对的复合产物。**

### 论证

① 反射对复合 = 旋转（相位生成元，§一）∧ ② 相位 = 旋转轨道（§二）∧
③ 相位轴 = S 取反特征空间（§三）∧ ④ 相位产生 = 升维（§四）∧
⑤ 相位锚定 = 互逆对和 = 0（§五）。

### 形式化（PhaseGeneration.lean，1 定理）

- `phase_generation_synthesis`：五段合取——相位产生机制合一。

---

## 参考文献

- R047（发散/周期 = 共轭对称性特征空间），claims/Toolkit/R047.yaml
- R083（S/R 同属 T 家族，MirrorRotationDecomposition.lean），claims/Toolkit/R083.yaml
- R085（0 = ±1 折叠类），claims/Toolkit/R085.yaml
- R136（方向声明定序），claims/Toolkit/R136.yaml
- R138（相位关系锁定），claims/Toolkit/R138.yaml
- R227（零依赖几何，DivergencePeriodGeometric.lean），claims/Toolkit/R227.yaml
- R228（0 的依赖，ZeroDependence.lean），claims/Toolkit/R228.yaml
- R231（维度升降，DimensionSymmetry.lean），claims/Toolkit/R231.yaml

* · 课后习题 Pat0-1 · 2026-08-14 · 相位产生研究 · 主要作者: Deepseek（形式化）; 用户（方向/框架 claim/命名）· Lean: 形式化/Formal/Toolkit/PhaseGeneration.lean（唯一真源）· 论文: pat_phase_generation.md（研究版）*
