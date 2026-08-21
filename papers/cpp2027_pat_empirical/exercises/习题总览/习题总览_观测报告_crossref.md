# 课后习题 I：内容详细对照（与原文逐项比对）

> **声明 (Declaration)**: 本文**不代表任何数学结论**, 仅为基于 Lean 4 形式化的一种**实验观测报告** (对照文档)。
>
> | 习题 | 主题 | Lean 形式化 | DOI |
> |---|---|---|---|
> | exercise_i_crossref | 习题 I 内容详细对照 | PatPvsNPExercise.lean | DOI |
>


> 本对照文档服务对象：`习题总览_观测报告.md`（R157，4 新定理）。逐项核对习题每个论点的锚定来源——题面（R152/R153 侧写）→ 解答（R157 展开）→ 源定理（ Lean 定理），三列对齐。全部源定理可复验：`形式化/Formal/Toolkit/*.lean`。

*2026-08-13 · 对照文档 · 无新增 claim（仅比对，不产生新定理）*

> 外部文献对照（全字段书目 + 验证记录 + 健在/已故标注，85+ 条）见`../shared/对照说明.md`（共享引用清单）（引用清单），并已同步进 `literature/references.bib`。

---

## 一、对照总览

| 习题章节 | 习题论点 | 锚定 claim | 锚定 Lean 文件 | 对照结论 |
|---|---|---|---|---|
| 零、总论 | P vs NP = 发散/收敛互锁对的投影 | R047 / R147 / R148 | CausalityTime / InterlockIsomorphism | 论点 = R148 互锁同构的计算投影，无新增 |
| 一、结构找回精确 | 验证 = 查表判等（双向） | R152 ② / RulerLookup / RulerRevLookup | ConciseMagicTeaching | ★新定理 lookup_iff_value：R152 verification_free 单向 → 双向 |
| 二、模糊与结构等价 | witness ⟺ 表条目（双向） | R153 ④ / RulerLookup | ConciseMagicTeaching / PatNondeterminism | ★新定理 witness_iff_table_entry：R153 np_witness_in_table 单向 → 双向 |
| 三、★NP 模糊/结构对偶 | 模糊存在性 ∧ 结构判等 | R147 / R152 / R153 / R150 | 本习题新定理 | ★新定理 np_fuzzy_structure_duality：核心，前两定理组合 |
| 四、全景 | N=外推 ∧ 验证=判等 ∧ P=锁定链 | R150 / R152 / R153 ① / R050 | PatCountableInfinitPhaseUnification / PatNondeterminism | ★新定理 p_np_pat_perspective：全景组合 |

**一句话对照**：习题没有发明新结构——四个新定理都是已有定理的**双向化**（单向→双向）与**组合化**（分离→对偶/全景）。这正是"用结构找回精确"在形式化层面的体现：锚定结构不变，论证收束。

---

## 二、定理级对照（R157 新定理 ↔ 源定理，逐证明步骤）

### 2.1 `lookup_iff_value` — 验证 = 查表判等（双向）

```lean
theorem lookup_iff_value {D E} [Fintype D] [DecidableEq D] [DecidableEq E]
 (f : D → E) (x : D) (y : E) : y = f x ↔ (x, y) ∈ makeTable f
```

| 证明步骤 | 使用的源定理 | 来源 | 与原题面（R152）的关系 |
|---|---|---|---|
| 正向 `y = f x ⟹ 表条目` | `rw [h]` + `lookup_exists` | ConciseMagicTeaching（RulerLookup 表全量） | R152 `verification_free` 只给 `(x, f x) ∈ makeTable f`（特例） |
| 反向 `表条目 ⟹ y = f x` | `lookup_correct` | ConciseMagicTeaching（RulerLookup 表值 = 函数值） | R152 未给反向；**习题新增双向** |
| 值域多态 `[DecidableEq E]` | — | 习题修正（验证函数 Bool 值域，非 D→D） | 初版错写 D→D，已修正 |

**对照结论**：R152 verification_free 是 lookup_iff_value 在 y = f x 时的特例（代入即得）；lookup_iff_value 是 RulerLookup 两个单引理（lookup_exists/lookup_correct）的 iff 组合。

### 2.2 `witness_iff_table_entry` — witness ⟺ 表条目（双向）

```lean
theorem witness_iff_table_entry {D} [Fintype D] [DecidableEq D]
 (V : D → D → Bool) (x : D) :
 (∃ w, V x w = true) ↔ (∃ w, (w, true) ∈ makeTable (fun w => V x w))
```

| 证明步骤 | 使用的源定理 | 来源 | 与原题面（R153）的关系 |
|---|---|---|---|
| 正向 `witness ⟹ 表条目` | `rw [h]` + `lookup_exists` | ConciseMagicTeaching | 与 R153 `np_witness_in_table` **完全相同**（习题复用） |
| 反向 `表条目 ⟹ witness` | `lookup_correct` 反向（`.symm`） | ConciseMagicTeaching | R153 未给反向；**习题新增双向** |

**对照结论**：R153 np_witness_in_table 是 witness_iff_table_entry 的正向合取；反向由 lookup_correct（表值 = 函数值 ⟹ true = V x w ⟹ V x w = true）封死。**模糊（witness）与结构（表条目）等价**的论证核心是 RulerLookup 的 lookup_correct。

### 2.3 ★`np_fuzzy_structure_duality` — NP 的模糊/结构对偶（核心新定理）

```lean
theorem np_fuzzy_structure_duality {D} [Fintype D] [DecidableEq D]
 (V : D → D → Bool) (x : D) (hw : ∃ w, V x w = true) :
 (∃ w, (w, true) ∈ makeTable (fun w => V x w)) ∧
 (∀ w, V x w = true ↔ (w, true) ∈ makeTable (fun w => V x w))
```

| 证明步骤 | 使用的源定理 | 来源 |
|---|---|---|
| 前半 `结构存在性` | `witness_iff_table_entry .mp` | 习题 2.2（其反向即 R153+lookup_correct） |
| 后半 `逐点判等` | `lookup_iff_value`（逐点实例化） | 习题 2.1（RulerLookup 双向） |

**对照结论**：本题核心定理无新锚——是 2.1 与 2.2 的机械组合，但语义是新的：**"模糊存在性 ⟹ 结构存在性 ∧ 逐点判等"把 R153 的"NP 存在性 = 验证表条目"从单向断言升级为对偶结构**。对应论证：求解（前向，发散）与验证（后向，收敛）= R147 互锁对（CausalityTime.causality_pair_reduces: (f-e)+(e-f)=0）。

### 2.4 `p_np_pat_perspective` — 全景（N=外推 ∧ 验证=判等 ∧ P=锁定链）

```lean
theorem p_np_pat_perspective {D} [Fintype D] [DecidableEq D]
 (V : D → D → Bool) (x : D) (θ : ℝ) (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 2 * Real.pi) :
 (∀ ε, 0 < ε → ∃ y ∈ patGrid, |θ - y| ≤ ε) ∧
 (∀ w, V x w = true ↔ (w, true) ∈ makeTable (fun w => V x w)) ∧
 (∀ d, Function.Injective (fun x : ℝ => x + d))
```

| 合取项 | 使用的源定理 | 来源 | 对应题面 |
|---|---|---|---|
| ① N = 相位锁定外推 | `pat_phase_unification`（王氏定理） | PatCountableInfinitPhaseUnification（R150） | R153 ③（nondeterminism_is_phase_locking_extrapolation 同款） |
| ② 验证 = 查表判等 | `lookup_iff_value` 逐点 | 习题 2.1 | R152 ②（verification_free 双向化） |
| ③ P = 锁定方向唯一链 | `deterministic_locked_chain_unique` | PatNondeterminism（R153 ① / R050 机制） | R153 ① 直接复用 |

**对照结论**：全景定理 = R150（王氏）⊕ R153 ①（P）⊕ 习题 2.1（验证）——三根支柱在 P vs NP 上的合取。R153 nondeterminism_pat_perspective 是 (①②) 子集；习题全景新增 ③ 验证判等项并锚定 P。

---

## 三、题面对照：R152/R153 说了什么，R157 补了什么

| 原题面 claim | 原定理（数量） | R157 对照 | 增量性质 |
|---|---|---|---|
| R152 有限域上 P=NP 平凡 | finite_domain_P_eq_NP | 习题四论证引用，无新定理 | 复用 |
| R152 验证 = 可逆查表后向免费 | verification_free（单向） | lookup_iff_value（双向） | **双向化** |
| R152 求解/验证 = 发散/收敛互锁对 | solve_verify_dual | 习题三论证引用（causality_pair_reduces） | 复用（论证层） |
| R153 ① P = 锁定方向唯一链 | deterministic_locked_chain_unique | 习题四 ③ 合取项直接复用 | 复用 |
| R153 ② N = 未锁定多路径 | nondeterministic_multiple_paths | 习题四论证引用（未锁 = 模糊） | 复用（论证层） |
| R153 ③ N = 相位锁定外推 | nondeterminism_is_phase_locking_extrapolation | 习题四 ① 合取项（同源 R150） | 复用 |
| R153 ④ NP 存在性 = 验证表条目 | np_witness_in_table（单向） | witness_iff_table_entry（双向） | **双向化** |
| R153 ⑤ N 的 Pat 视角组合 | nondeterminism_pat_perspective | np_fuzzy_structure_duality + p_np_pat_perspective | **组合化+对偶化** |

**增量清单（R157 独有的 4 个定理）**：
1. `lookup_iff_value`：验证判等双向（R152 未给反向）。
2. `witness_iff_table_entry`：witness⟺表条目双向（R153 未给反向）。
3. `np_fuzzy_structure_duality`：模糊/结构对偶（新组合，核心）。
4. `p_np_pat_perspective`：全景合取（R150⊕R153①⊕习题①）。

---

## 四、论证链对照（习题章节 ↔ 章节）

| 习题章节 | 论证步骤 | 对应章节/claim |
|---|---|---|
| 零、总论 | 发散/收敛互锁对投影 | ·十二（R147 因果与时间，causality_pair_reduces）；·十三（R148 互锁同构） |
| 一、①表=结构 | 有限域函数=预计算表 | ·RulerLookup（function_is_table）；R057 一切皆表 |
| 一、②验证不重算 | 查表判等 | ·R152 ②（verification_free） |
| 二、①单向已有 | R153 np_witness_in_table | ·十八（R153 ④） |
| 二、②反向封死 | lookup_correct 表值=函数值 | ·RulerLookup（lookup_correct） |
| 三、①模糊换速度 | N 存在性由相位锁定外推 | ·十七·十八（R150 王氏定理 / R153 ③） |
| 三、②结构找回精确 | 表判等还原真值 | ·RulerLookup/RulerRevLookup |
| 三、③互锁对 | 发散端存在性/收敛端精确性 | ·十二（R147）；R047 发散/收敛同一对称性 |
| 四、①N=外推 | pat_phase_unification | ·十六（R150 王氏相位锁定性定理） |
| 四、②验证=判等 | lookup_iff_value | ·十七（R152）+ RulerLookup |
| 四、③P=锁定链 | deterministic_locked_chain_unique | ·十八（R153 ①）；R050 机制；R136 方向声明 |
| 四、④有限域平凡 | 表全量 ⟹ 模糊不必要 | ·十七（R152 ① finite_domain_P_eq_NP） |
| 四、⑤诚实边界 | 非 P≠NP 判定 | ·十七（R152 诚实边界原句延续） |

**结论**：习题全部论证步骤都能在找到章节级落点，无悬空引用；新增内容只发生在"双向化/组合化"层面。

---

## 五、术语对照

| 习题术语 | 对应概念 | 锚定 |
|---|---|---|
| 模糊（N 的存在性） | 未锁定相位 | R140 single_symmetry_underdetermines（未锁定 ⟹ 位置不唯一）；R138 未锁定 = 自指坍缩 |
| 速度（换来的） | 不穷举的存在性 | R150 王氏定理（任意精度统一，不依赖搜索路径） |
| 结构（表） | 预计算表 / 一切皆表 | RulerLookup（makeTable）；R057 存储⟷计算同构 |
| 精确（找回的） | 判等还原真值 | lookup_correct（表值 = 函数值） |
| 锁定链（P） | 方向锁定的唯一链 | R050（迭代单射）；R136（成对一次性声明）；R137（pat n = pat0+n·d） |
| 互锁对 | 求解/验证 = 发散/收敛 | R147（causality_pair_reduces）；R047（发散/收敛同一对称性） |

---

## 六、诚实边界对照

| 边界 | R152 原文 | R157 延续 | 对照 |
|---|---|---|---|
| 判定边界 | 完整 P≠NP 需要计算模型下界证明 | 习题仅交付结构侧写 | 一致，无突破 |
| 定理边界 | 4 定理均为有限域/保留日志条件 | 4 新定理同样限 Fintype D | 一致（Fintype 前提继承） |
| 引理边界 | R153 用户纠正：不用外部引理 | 习题全部锚本框架定理 | 一致，无 mathlib 独有引理（仅 ring/simp 基础） |

---

*课后习题 I 对照文档 · 2026-08-13 · 无新增 claim，仅比对（源定理全部可复验于 形式化/Formal/Toolkit/）*
