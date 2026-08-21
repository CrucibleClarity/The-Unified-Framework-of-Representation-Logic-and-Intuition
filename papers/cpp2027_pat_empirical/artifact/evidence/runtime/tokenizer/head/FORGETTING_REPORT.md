# tokenizer 注意力优化报告（keahas-0.8 融合）

> 2026-08-13 · 优化 tokenizer 体系: 遗忘曲线反馈循环 + 连接池管理融入 head 层

## 一、优化内容

**新文件**: `src/repo_v5/tokenizer/head/forgetting.py`

| 结构 | 职责 | 融合源 |
|---|---|---|
| **TokenForgettingCurve** | token 使用频率指数衰减 → 注意力权重调节 | keahas-0.8 ForgettingCurve (Ebbinghaus) |
| **TokenConnectionPool** | token 引用连接 (定义链) 复用/回收 | keahas-0.8 ConnectionPool |
| **TokenizerAttentionV8** | 注意力 = 结构信号 (brace/bracket) × 遗忘曲线权重 | head/attention 融合 |

## 二、优化原理

1. **遗忘曲线 → 注意力权重**: 高频 token (近期使用) 复习巩固 → 权重高; 低频 token 衰减 → 适度遗忘 (注意力不浪费)
2. **反馈循环**: 衰减边缘 token = 需要复习的信号 (feedback) — 类似 spaced repetition
3. **连接池**: token 定义引用连接池化 — 不重复 expand (bracket_vec 解析复用)
4. **注意力公式**: attn_weight = structure_sig (brace 深度) × freq_weight (遗忘曲线) — 结构与频率的乘积

## 三、验证（真实 token 序列: addition 定义链）

```
D:100 addition     attn=0.880 freq=0.800  (高结构 + 高频)
D:102 equals_arith attn=0.880 freq=0.800
D:179 succ         attn=0.880 freq=0.800
D:117 value_zero   attn=0.880 freq=0.800
D:138 truth_true   attn=0.347 freq=0.800  (低结构信号 → 注意力低)
```

- 连接池: 19 条引用连接建立 (addition 定义链)
- 注意力区分: 结构信号差异 → 注意力权重差异 (0.88 vs 0.35)

## 四、对应框架

| tokenizer 优化 | 框架/keahas 对应 |
|---|---|
| TokenForgettingCurve | Ebbinghaus 遗忘曲线 / RulerErrorSeq |
| TokenConnectionPool | R161 连接级信息素 / keahas-0.8 |
| 注意力 = 结构 × 频率 | R082 (token 快路径) / R150 (无限注意力) |
| 反馈循环 (低频复习) | RulerSelfRepair (反馈修正) |

## 五、文件

- 新增: `tokenizer/head/forgetting.py` (自包含, 只经权威接口)
- 融合: keahas-0.8 → tokenizer head 层
