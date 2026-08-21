# CPP 2027 Submission — Empirical Foundations of Pat

> 本包是 ACM CPP 2027 提交包 (`cpp_submission_pat`): 从
> `selfcontained_zh`(Pat 实证自包含包)提取的**通过 transformer 实证
> 研究证明 Pat 的过程** — 训练观测 → 结构规律 → 框架对照 → 逻辑完备
> 判定 → Lean 机器验证定理。论文 + artifact 均双盲 (匿名)。

## 0. 发布定位: 人机合作证明视角

**本次发布是针对人机合作证明 (human–AI collaborative formalization)
视角下的论文发布。**

- **人机分工**: 论文记录的实证→形式化链路由人与 AI 助手合作完成 —
  人类提供方向、框架 claim (R136/R138/R143/R149/R150/R151/R163)、
  观测判定与纠正 (如"四定理中第三定理是逻辑完备定理"这类定位修正);
  AI 助手辅助形式化 (Lean 证明)、观测记录与数据分析。
- **可验证核心在人**: 论文的可验证资产是 22 条 Lean 机器检查定理
  (0 sorry, `lake build` 通过) — 机器检查证明是论文主体, 人机协作
  是产生过程与方法论视角, 不进入证明本身。
- **双盲**: 人机分工记录 (谁提方向/谁写证明) 不包含任何作者身份信息。

**CPP 适配性**: 适合。CPP (Certified Programs and Proofs) 的主题是
机器检查证明与证明工程; 本论文的 formalization track 定位 —
22 条 Lean 定理、标准公理、pinned 工具链、可复现 artifact — 正是
CPP 的核心 scope; 而 AI-assisted formalization (LLM 辅助证明) 是
CPP 近年持续关注的方向。人机合作证明视角作为方法论交代, 与双盲
提交不冲突 (审稿人只需验证 Lean 定理本身)。

## 1. ACM 提交表单 — 复制粘贴即用

> 表单要求三个字段 (Title / Submission PDF / Abstract)。
> 下面的代码块内容可直接复制粘贴;Abstract 支持 Markdown + LaTeX 数学 ($...$)。

### Title (复制粘贴)

```
Empirical Foundations of Pat: Transformer OOD Observations, Structural Laws, and Machine-Checked Continuum Theorems
```

### Submission PDF (上传)

```
Empirical_Foundations_of_Pat.pdf   (本包根目录, 6 页, 约 130 KB)
```

### Abstract (复制粘贴)

```
We record the empirical route by which the Pat framework is grounded:
starting from controlled transformer training observations, extracting
structural laws, and ending in machine-checked theorems. The starting
observation is a two-pole out-of-distribution (OOD) dichotomy,
reproduced in 45 training runs: a low-epoch transformer reaches training
accuracy 1.000 on successor-notation arithmetic, yet OOD accuracy is
32/32 on length extrapolation in the trained notation and 0/32 on the
same structure written in an untrained notation of the same basepoint;
adding explicit equivalence statements bridges the two notations
(0/32 → 32/32). From this and supporting experiments we extract five
structural laws (anchor binding, notation translatability, shift
invariance, structure-bearing representation, definition-layer
invisibility). The laws map, as an observational correspondence, to the
Pat framework's paired-direction declaration, phase-relation locking,
and phase-magnitude interlock. A completeness criterion — the decoupling
operator D (exclusion + cancellation + layering) implying completeness
at any order, element, and subject-object — organizes the
correspondence, and three mapping judgments (symbol-norm,
presentation-legality, intuition-precision) give the layer-to-layer
verdicts that the OOD two-pole dichotomy exhibits.

The framework chain is formalized in Lean 4 / mathlib: twenty-two
theorems with zero errors and zero sorry, from the interlock matrix
(determinant θ·(r + 1/r) ≠ 0) through the four-phase interlock, the
countable pat grid, and the density theorem, to the continuum closure
theorems (the continuum [0, 2π] is the closure of the pat grid; an
endogenous version constructs the same closure from two paired
basepoints and midpoint reduction). Toolchain: Lean 4.32.2 + mathlib
v4.32.2 (pinned), standard axioms (propext, Classical.choice,
Quot.sound), lake build passes, zero sorry.

The honest boundary is stated exactly: the empirical-to-framework
mapping is an observational correspondence, not a deductive
implication, and the training results are reproducible from the
artifact (one command, Python + PyTorch). Classical components are
marked KNOWN in the claim ledger.
```

## 2. 提交元数据

- **Track**: CPP (Certified Programs and Proofs) 2027, formalization track
- **Anonymous**: 论文 + artifact 无作者 / 邮箱 / 机构 / DOI / 仓库标识
- **注册截止**: 2026-09-03 (AoE) · **完成截止**: 2026-09-10 (AoE)

## 3. 论文写作纪律 (逐段写)

论文 (及本系列全部提交包) 按**逐段写**纪律成文: 每段一个内容单元,
写完自查 (逻辑/直觉/符号/呈现四要求), 确认后再进下一段, 禁止一次成文。

**目标**: 防止单次输出上限导致的精度丢失 — 一次成文 = 长输出后段
精度下降 (上下文衰减/注意力漂移), 逐段写使每段可独立校验, 每段在
输出预算内完成, 精度不随总长度衰减。

## 4. 包结构

```
cpp_submission_pat/
├── Empirical_Foundations_of_Pat.tex   # 论文源码 (acmart sigplan, anonymous)
├── Empirical_Foundations_of_Pat.pdf   # 编译产物 (tectonic, 6 页)
├── README.md                          # 本文件 (发布说明)
├── refs.bib                           # 20 条引用 (全部真实文献, arXiv/Crossref 核验)
└── artifact/
    ├── README.md                      # artifact 构建说明 + 定理清单 + 溯源
    ├── formal/                        # Lean 形式化 (26 文件最小闭包 + lakefile +
    │   │                              #   lean-toolchain + claims 台账)
    │   └── claims/                    #   R136/R138/R143/R149/R150/R151/R163 + R031
    └── evidence/                      # E12 训练实证 (一键复现 + 运行时快照 + 结果)
```

## 5. 论文内容 (五节)

1. **实证起点** — E12: 训练 acc 1.000, OOD 两极 (同记法 32/32 ↔ 同基点
   零样本 0/32 ↔ 等价声明桥接 32/32), 45 次训练跨运行逐 seed 复现;
   判定口径 = 完整序列逐 token 重建 (位置级 acc 不可信)。
2. **五条结构规律** — 锚绑定 (E11), 记法可翻译 (E12), 平移不变 (E9),
   结构承载 (E6), 定义层不可见 (E4/E5); 元规律: 训练直觉 = 表示绑定的统计。
3. **框架对照** — 锚 ↔ 成对声明 (R136), 等价声明 ↔ 对称对还原 (R143),
   双向可译 ↔ 互锁矩阵非奇异, 未声明 ↔ pat0 坍缩 (R138) — 观测性对照,
   非演绎证明。
4. **完备性判定与映射判定** — 解耦算子 D (排除 + 对消 + 分层) ⟹ 任意阶/
   任意元/任意主客体完备; 三个映射判定 (符号规范 / 呈现合法 / 直觉精确)
   = OOD 两极的训练层展现; 符号→呈现补全五层覆盖。
5. **机器验证定理** — 22 定理 0 sorry: 互锁矩阵 (R143) → 四相位互锁
   (R149) → 可数格点 + 稠密 (R150) → 连续统闭包 (R151) → 内生闭包
   (R163); 映射判定 5 定理 (MappingJudgmentTheorems.lean)。

## 6. 编译方法

```bash
# 论文 (tectonic)
tectonic Empirical_Foundations_of_Pat.tex

# Lean 形式化 (需 lean 4.32.2 + mathlib v4.32.2)
cd artifact/formal && lake build

# 训练实证 (python3 + torch)
cd artifact/evidence && python3 run_all.py
```

## 7. 双盲检查 (发布前必检)

- [ ] 论文 + artifact 无作者 / 邮箱 / 机构
- [ ] 无 DOI / 仓库标识 / 本地路径
- [ ] 无 hash 相关内容
- [ ] 论文中不出现 "logical completeness theorem / intuition theorem /
      symbol theorem / presentation theorem" 字样 (写作四要求不引用为定理名)

## 8. 溯源

- 源包: `src/repo_v5/lab/paper_repro/selfcontained_zh/`
  (Pat 实证自包含包, 2026-08-16 快照)
- 本包提取链路: 实证 (E12 一键复现 + 结果快照) → 结构规律 → 框架对照 →
  完备性判定 → Lean 形式化 (26 文件闭包, 含 claims 台账)
- 相关提交: `cpp_submission_pat_trail/` (完整研究轨迹版, 含时间线与
  证据链; 本包为聚焦"实证证明 Pat 过程"的独立论文)

### Originality statement

This research was conducted through an API, and the model capability
has been distilled; the conflict scope cannot be confirmed.
Originality is evidenced only by session logs and git backup
timestamps.
