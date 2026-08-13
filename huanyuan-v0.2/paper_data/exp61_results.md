# EXP-61: 语法模糊对照 (G0/G6) — 结果记录 (修正版)

日期: 2026-08-11 | 命题: 形式→构造 (语法→训练速度)

## 修正历史

原 EXP-61 (定义模糊: 移除 law/definition) 做错 — 测的是数据缺失非语法, 已废弃。
修正为**模糊语法** (G/P 层排列方法), 分两阶段:
- EXP-61g: 单独 prefix vs infix (语法格式)
- EXP-61h: 干扰 token 探测直觉/结构 (见 exp61h_intervention_probing.md)

## EXP-61g 结果 (互逆概念对一起训练, 用户建议)

**配置**: 逻辑门 + 互逆门对 (and↔or, xor↔xnor via interdef/arrow) + 9 门 law
(含负例, 修复 _law_result_neg 支持 truth 结果) + 算术支撑 (addition balanced)。
1000 样本, 15 epochs。**前提: 要能学习, 得挑互逆概念对一起训练**
(单看一个概念学不会 — 纯逻辑门 730 样本 OOD 0.092; 加互逆对后 0.927+)。

| 指标 | prefix | infix |
|---|---|---|
| 判定口径 (权威 OOD) | 0.836 | 0.853 |
| epoch_gen_all (最后) | — | 0.952 |
| epoch_gen_no0 (剥离0acc, 最后) | — | 0.983 |
| 判定口径 (训练日志) | 0.927 | 0.931 |

## 结论 (用户观察确认)

1. **单独 prefix vs infix 差异小** (0.836 vs 0.853, Δ0.017) — 语法格式
   本身不决定学习差异。**用户观察正确**: 单独对比两个格式, 一个成功率高/
   泛化好, 一个低/差的现象**不出现** — 需要更强干扰才能显影差异。
2. **互逆概念对是学习前提** (重要发现): 单训练一个概念 (无对偶) 学不会;
   and↔or/xor↔xnor 等互逆对同训后学会 (0.092→0.927)。这与 G2
   (平行概念) 一致 — 概念从与它对偶的关系中学习。
3. **law 负例修复**: _law_result_neg 原只支持 value 结果, 逻辑门
   (truth 结果) 无负例 — 已修复, 9 门 law 现含同构结果错负例。
4. **剥离不彻底是方法论的强**: 用户指出"方法论太强, 很难剥离干净" —
   不强求剥离, 用**干扰**显影差异 (EXP-61h 方向)。

## EXP-61h (待实现)

干扰 token 探测直觉: 将 op 拆成两个相同 token, 观察直觉 (均匀分布) vs
结构 (集中) 分化。设计见 exp61h_intervention_probing.md。

## 配置与归档

- configs: exp61g_prefix_only.json / exp61g_infix_only.json (docs/paper_data/configs/)
- runs: exp61g_prefix_only_20260811_222924 / exp61g_infix_only_20260811_223436
- 代码: blur_grammar_samples (lab/synth_core.py, 混用语法), _law_result_neg (truth 支持)
