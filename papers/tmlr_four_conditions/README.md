# TMLR Submission — Verifiable Design Conditions for Symbolic Training

**Title:** When Does Symbolic Training Generalize Out-of-Distribution?
Four Verifiable Design Conditions and an Ablation of the Decoupling Operator

**Venue:** TMLR (Transactions on Machine Learning Research) — 2026-08-21 状态

**File:** `Verifiable_Design_Conditions.tex` → `Verifiable_Design_Conditions.pdf` (8 页正文)
**编译:** `tectonic Verifiable_Design_Conditions.tex` (tectonic 1.0+, 无外部依赖)

## 论文定位 (ML 化改写)

本包是原 CPP 四定理包的 TMLR 版:

- **问题**: 符号训练信号的 token 设计如何决定 transformer 的 OOD 泛化?
- **贡献 1**: 45 runs 复现两极点模式 (E12: 32/32 vs 0/32 vs 声明后 32/32)
- **贡献 2**: 四个可验证设计条件 (信号完备/符号规范/呈现合法/直觉精确), 每个有两极点实验设计 + Lean 4 形式化 (5 定理, 0 sorry)
- **贡献 3**: decoupling 算子消融 (42 fresh runs) — layering 违反致命 (序列 0/3, 双角色位置崩), 声明缺失封顶 (per-token 0.238, 仅共享结构位置达 1), exclusion 污染拖慢收敛 (peak 24.3→27.7), 两个 cancellation 操纵均为 null result (单向呈现 + 覆盖范围不足 — 诚实报告, 界定该子句的鲁棒性边界)
- **贡献 4**: per-token OOD 曲线 + peak-epoch 标签 + **位置级标签** (每位置达到 OOD=1 的 epoch) 作为诊断工具 (区分被序列级准确率混淆的失败模式)

## 作者与 AI 声明

- 独立研究者;研究由作者主导,通过 DeepSeek (商业 API 模型) 执行
- 模型能力已被蒸馏;本文表述 = 作者主导下对被蒸馏内容的还原期望
- 完整协作记录 (session log, 阶段分类, artifact) 可供审计
- 双盲投稿: 论文中作者为 Anonymous, 无身份/邮箱/机构/DOI/仓库标识

## 引用

- `refs.bib`: 44 条 (从 CPP 版 126 条裁剪: 保留 ML/认知/形式化核心, 哲学符号学压为 related work 段)
- 引用纪律: 全部在正文定位使用, 无死条目

## 实验与可复现

权威实验包: `src/repo_v5/lab/paper_repro/selfcontained_zh/`
(2026-08-16 快照, 完整自包含 runtime 含 archive 模块)。
本包 artifact 为该包的拷贝 + 消融脚本, 已验证可在仅 python3+torch
环境下独立复现 (不含任何 src 路径依赖)。

```
artifact/evidence/
├── runtime/                # 完整自包含运行时 (tokenizer/train/synth/archive/lab)
├── succ矩阵实验.py          # succ 结构对比矩阵 (E12 主实验, 权威版)
├── ablation_exp.py         # 消融: decoupling 三子句 + 多配置 (108 runs, 主组 10 seeds/条件)
└── results/
    ├── run_all_out.txt     # E12 原始输出
    ├── ablation_curve.tsv  # 逐 epoch per-token OOD 曲线 (2341 行, 39 runs × 60 epochs)
    └── ablation_summary.tsv # 汇总 (peak_epoch / hit_one / norm_pt, 40 行)
```

运行:

```bash
# 需要: python3 >= 3.12 + torch >= 2.0 (任何环境, 无其他依赖)
cd artifact/evidence
PYTHONPATH=runtime:runtime/lab:<venv site-packages> \
    python ablation_exp.py     # 消融 108 runs (~10 分钟 GPU)
PYTHONPATH=runtime:runtime/lab:<venv site-packages> \
    python succ矩阵实验.py      # E12 复现 15 runs
```

验证记录 (2026-08-22, selfcontained_zh 权威环境重跑):
- succ矩阵实验: ①a 32/32, ①b 0/32, ② 32/32, ②' 32/32, ④ 32/32 (各 3 seeds)
- 消融 108 runs 全部完成 (主组 10 seeds/条件), 统计检验: 污染 30% 显著拖慢 (p=0.038); n_align 对照排除样本数混杂; canc_partial 边缘 (p=0.06)
- 图: **fig_theorems.png** (主图, 2x2 四定理两极点面板, 由 make_figures_v2.py 生成 — 极端干净版: 无网格/单色系/数值直标) + fig1_curves.png (per-token OOD 曲线) / fig2_positions.png (位置级热图) / fig3_peak.png / fig4_id_ood.png (ID vs OOD, 附录), 由 make_figures.py 生成
- 统计: stats_test.py (零依赖 Welch t-test + Mann-Whitney U)

消融输出指标 (用户指定的标签设计):
- `pt_ood`: per-token OOD 重建正确率 (逐 token argmax vs 目标)
- `seq_ood`: 序列级 (全对) 正确率
- `peak_epoch`: 第一个 per-token OOD == 1.0 的 epoch; 未达 1.0 则取达到最大 per-token OOD 的 epoch
- `hit_one`: 是否达到过 per-token OOD == 1.0
- `norm_pt`: per-token OOD(final) / peak_epoch (归一化恢复)
- **位置级** (`ablation_pos_curve.tsv` / `ablation_pos_summary.tsv`):
  每个绝对位置 j 的 OOD 曲线 + 每位置 `peak_epoch_j` / `hit_one_j` / `norm_j`
  (该位置达到 OOD==1.0 的 epoch; 未达 1 取该位置最大 OOD 的 epoch)
- **ID 对照** (`ablation_id_curve.tsv`): 训练集内 per-token 曲线 (前 64 样本),
  证明训练内收敛 vs OOD 崩的对照

位置级关键发现 (main 组, 3 seeds):
- no_decl: 仅 pos 0-1 (判定头/外括号 = 共享结构) 达 1, 算术核心位置永不达 1 → 0.238 的精确构成
- layer_dual: 双角色符号的 bracket 角色位置 (pos 1) 永不达 1, 内部位置随之失败;
  op 角色位置 (pos 2) 恢复 → 角色混淆定位在冲突角色的位置

## 与系列其它包的关系

| 包 | 定位 |
|---|---|
| `cpp_submission_pat` | PAT 框架主论文 (CPP, Lean 19 定理) |
| `cpp_submission_four_theorems` | 四定理重述 (CPP 版, DOI DOI) |
| **`tmlr_submission_four_theorems`** | **本包: ML 化四条件 + 消融 (TMLR)** |
| `colm_submission_Intuition_Construction` | AI 视角直觉诱导 (COLM) |
| `cognition_Intuition-Construction` | 人类视角认知论文 (暂缓) |

## 发布与提交状态

- **双盲仓**: 已上传 `papers/tmlr_four_conditions/` (CrucibleClarity 匿名仓, 446 文件, 2026-08-22)
  - 上传匿名化: 身份/路径/DOI 清除 + 敏感凭据替换 (会话记录中粘贴过的真实 token → REDACTED)
  - 工具: `tools/upload_tmlr_package.py` (幂等, sha 对比)
- **submission zip**: `/tmp/tmlr_submission_20260822.zip` (论文 tex/pdf + bib + 主图 + README)
- **数字审计**: 论文全部数字与 108 runs 实验汇总一致 (decl_full 行已修复, peak 范围 14--41, bib 46=46)

## 提交前待办

- [ ] 换 TMLR 官方模板 (当前为 article+natbib 近似; 需在宿主侧下载 iclr 模板后替换)
- [ ] 图终检: 用 deepseek-v4-flash-vision-exp 新会话目视 fig_theorems.png
- [ ] OpenReview 提交时填写 Ethics / AI 使用声明 (论文已含 AI assistance statement)
