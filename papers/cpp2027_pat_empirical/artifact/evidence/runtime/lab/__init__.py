"""lab/__init__.py — 自包含包精简版

原仓库 lab/__init__.py re-export 全栈 (tokenizer.head / infer / verify /
experiment / diag 等)。本自包含包仅承载 E12 实证链所需子模块
(lab.judge / lab.synth_core / lab.gen_all_ops / lab.runner),
因此 __init__ 不 re-export 任何名字; 子模块直接引用不受影响
(from lab.judge import judge_sequence 等)。

快照日期: 2026-08-16
"""
