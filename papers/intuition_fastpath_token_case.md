# 直觉构造驱动的 Lean 形式化: token 效率案例研究

**DeepSeek 辅助的黎曼方向经典结果形式化 (C011-C022)**

*内部研究笔记 — 2026-08-12*

---

## 摘要

本文报告一个案例研究: 借助 DeepSeek 语言模型, 通过"直觉构造"路径
(基点漂移、复平面投影、圆上整点、反演蜷曲等直觉框架), 在 Lean 4 +
mathlib 中将黎曼方向的一组**经典数学结果**全部形式化 (claims C011-C022,
全部 PROVED/KNOWN, 无 sorry, 全量 lake build 通过)。研究目标:
检验"直觉快速路径节省 token"假设。结果: 直觉确实快速命中已知结构
(免去教材式推导), 但单次 session 的 token 经济主要由传输效率决定
(99.2% 为上下文缓存重发), 实际新增内容 < 1%。**本文不声称证明
黎曼猜想或孪生素数猜想** — 所有形式化结果均为已知事实的重述,
零点的存在性/位置断言与孪生素数无穷性未触及。

## 1. 动机

用户最初的假设: 直觉快速路径 (intuition fast-path) 不只是节省推理
token, 还可能是数学结构的正确导航。为了验证, 用户提出一条直觉链:
"复数轴是某高维结构中 -1 的投影", "素数落在平移整数位", "1/2 是
反演-平移对偶的对称中心", "复数轴是蜷曲的, 无限与有限无差别",
"素数 = 圆上整点"。本 session 逐条形式化验证。

## 2. 方法

1. **直觉链 → 精确陈述**: 每个直觉先翻译为可判定的数学命题
   (群模型/复平面 ComplexAxis/高斯整数), 标记认识论标签
   (OBSERVATION/KNOWN)。
2. **Lean 形式化**: 在自建的 ComplexAxis (二维旋转代数, 投影 π,
   基点漂移) 上逐条验证, 全部定理 Lean 验收 (无 sorry)。
3. **Token 审计**: 沙盒记录全部模型请求 (state/requests.jsonl),
   统计传输字节与缓存命中率。

## 3. 结果

### 3.1 Claim 链 (全部 PROVED/KNOWN, 无 sorry)

| Claim | 直觉 | 形式化内容 |
|---|---|---|
| C011 | 复数轴 = 高维投影 | ComplexAxis 构造; J²=-1; 投影丢旋转/开方/基点位置; 实数轴是投影等价类 |
| C012 | 素数落平移整数位 | 素数只落基点一步 (n·p 素数 ⟺ n=1); 反演对偶 p/2 非整数; 无理轴无整数点 |
| C013 | 1/2 是对偶中心 | 部分和 = 反演轴整数位求和; s↦1-s 不动点 = 1/2; 临界线 ⟺ 1-s = conj s |
| C014 | 素数可被打出 | 两次漂移配方命中每个素数; 素数 = 高斯范数 (两平方和) |
| C015 | 轴是蜷曲的 | 反演把无限远卷回有限 (ε-R); 圆上整点 90° 循环 (R⁴=id) |
| C016 | 圆上整点结构 | 范数乘性; 整点环 (高斯整数); 轨道封闭 |
| C017 | 素数圆单轨道 | 两平方和分解唯一 (高斯整数 UFD) |
| C018 | 1/2 是复数开方 | 反射的平方根 φ∘φ = 反射 (i 的平方) |
| C019 | 临界线是圆 | 竖直线 x=1/2 反演 = 圆心 (1,0) 半径 1 的圆 |
| C020 | 两个圆 | 素数圆 (圆心 0) 与临界线圆 (圆心 1); 交叉: p=2 交点 1±i |
| C021 | 零点形状 | 非平凡零点 (猜想) 形状: 竖直线 ↔ 圆 (反演对合) |
| C022 | 一个圆 | 非平凡零点的圆 = 临界线圆 (同一个对象) |

### 3.2 Token 经济

```
模型请求:       1,009 次 (最后 12h 活跃期)
传输字节:       220,262,605 bytes
对话内容:       ~700k token ≈ 1.75M bytes
缓存命中率:     99.2% (上下文重发)
实际新增:       < 1%
```

## 4. 讨论

1. **直觉快速路径的省 token 假设: 部分成立**。直觉直接命中 KNOWN
   结构 (heap/torsor、两平方和、圆反演、函数方程对称轴), 免去了
   教科书式数论推导; 每个 claim 的平均形式化成本低。但 session 内
   大量反复确认同一组对象 (临界线圆/非平凡零点圆/半圆) 造成冗余,
   C019-C022 的实质可压缩至 <300k token。
2. **诚实边界**: 全部结果均为经典数学的重述 (novelty: KNOWN)。
   黎曼猜想的零点断言 (非平凡零点全在 Re(s)=1/2) 与孪生素数猜想
   (无穷多对 (p, p+2)) 均未证明, 也未产生任何新的部分结果。
   形式化位置几何 (临界线圆) 等价于函数方程对称轴的代数重述。
3. **蜷曲性与解析延拓**: C015 证明反演 (乘法结构) 的紧致性
   (无限远卷回有限), 对应解析延拓/拉马努金求和的机制 (ζ(-1)=-1/12)。
   但"无限问题消解"不等同于零点位置断言 — 这是两个独立问题。
4. **方法论教训**: 直觉构造是 KNOWN 结果的优秀组织/教学框架, 但
   不产生新定理; 形式化工具记录而不发明数学。

## 5. 案例: 基点漂移 — 复平面投影构造 (C011)

**直觉**: 复数轴是某高维结构中 "-1" 在人类数学空间 (实数轴) 的投影;
复平面上定义自然数 ⟹ λ 基点落在复数轴, 不在原点 0 而是 i (或 i 的
变换); 实数轴本身只是投影等价类。

**形式化过程** (全部在 `ComplexAxis.lean`):

1. **高维结构** — `ComplexAxis` (二维旋转代数 a + bJ, 乘法 = 复数
   乘法, ≅ ℂ 的矩阵表示): `J_sq`: J·J = -1 — 高维中 -1 有平方根
   (√(-1) 投影前存在)。`@[ext]` 注册结构外延。
2. **投影** — `proj (a+bJ) = a`: `proj_add` (保加法), `proj_J`
   (π(J) = 0), `proj_mul_not_preserved` (π(J·J) = -1 ≠ π(J)·π(J) = 0
   — 开方/旋转信息在投影中丢失)。
3. **根号 = 投影的逆** — `sqrt_neg_one_exists_high` (高维中 w·w = -1,
   w = J) vs `sqrt_neg_one_not_exists_axis` (实数轴上 ∀t, t² ≠ -1);
   `lift_neg_one_sqrt` (J·J = lift(-1)); `lift_add`/`lift_mul`
   (抬升保加乘, 实数轴是子代数)。
4. **基点漂移** — `basepoint` := i = J, `succ` (x ↦ x+1), `driftChain`
   := Chain(succ, i) (最小 σ-闭结构, 无 Nat primitive):
   - `basepoint_proj`: proj i = 0 — 原点假象 (投影把基点 i 显示成 0);
   - `pure_imag_proj`: 所有纯虚基点 ⟨0,b⟩ 投影都是 0 (i 的变换族);
   - `proj_succ`: π(σ(x)) = π(x)+1 — 后继投影 = 实数轴 +1;
   - `zero_in_proj_chain` / `proj_chain_succ_closed`: 投影后的链条是
     含 0 且 +1 封闭的自然数结构候选;
   - `proj_chain_basepoint_independent`: 任何纯虚基点给出同一投影
     结构 — 基点漂移在投影下不可观测。
5. **实数轴可疑性** — `axisLine b` (过纯虚基点 ⟨0,b⟩ 的实方向线),
   `axisLine_eval_proj` (线上点由投影值标定), `axisProjEquiv`
   (ℝ ≃ axisLine b — 每条线投影都是完整实数轴), `axisLine_proj_
   independent` (位置不可观测), `realAxis_indistinguishable_from_
   i_line` (实数轴 = 过 i 的线, 投影相同 — 假复数轴)。

**关键坑**: 结构分量投影需要 `@[ext]` 注册才能用 `ext`; 记号 `*`/
`+` 是实例字段, 需 `change` 显式展开成 `mul`/`add`; `0+0` 与 `0`
非定义相等, `rfl` 失败需 `ext <;> simp`; 投影不保乘法的数值验证
(π(J·J) ≠ π(J)π(J)) 需 `change` 到分量再 `norm_num`。

## 6. 结论

直觉构造驱动的形式化在 token 效率上可行 (直觉命中 + 缓存命中 =
实际成本极低), 但论文写作必须如实标注: 本案例形式化的是黎曼方向
的经典结果 (C011-C022, 全部 KNOWN), **不构成黎曼猜想或孪生素数
猜想的证明**。真正的差距 (零点的位置断言) 依然需要尚不存在的
数学论证。

## 7. 案例 A: "一窝八个" — 素数圆 8 整点的成对形式化

**直觉**: 素数 p ≡ 1 (mod 4) 的圆 x²+y² = p 上有 8 个整点 (一窝
八只), 而且它们成对。

**形式化过程** (定理全在 `ComplexAxis.lean`, 全量 build 通过):

1. **存在性** — `prime_two_axis`: p ≢ 3 (mod 4) 的素数 p 是
   ComplexAxis 中某点 z 的范数 (norm z = p), 即存在两轴坐标 (a,b)。
   直接引用 mathlib 的 Fermat 两平方和 `Nat.Prime.sq_add_sq`
   ([Fact p.Prime] + p % 4 ≠ 3 → ∃ a b, a²+b² = p), 由
   `exact_mod_cast` 收尾。这一层只给"有一个点"。
2. **8 个变体同圆** — `norm_neg_b` (norm ⟨a,-b⟩ = norm ⟨a,b⟩),
   `norm_swap` (norm ⟨b,a⟩ = norm ⟨a,b⟩), `rot90_norm` (旋转保持
   范数): 符号变体 (a,±b,±a,±b 交换) 与旋转变体全部落在同一个圆上。
   证明只是 `simp [norm]` + `ring`。
3. **轨道结构** — `rot90` (90° 旋转), `rot90_four` (R⁴ = id,
   4 循环), `rot90_keeps_lattice` (整点 → 整点), `orbit_closed`
   (旋转 × 共轭的轨道 ≤ 8 点全在同一圆上)。
4. **唯一性 (单轨道)** — `prime_sq_add_sq_unique`: 这是最重的一步,
   用高斯整数 UFD:
   - `gauss_unit_of_norm_one`: 范数 = 1 的高斯整数 = {±1, ±i}
     (分量枚举: re,im ∈ {±1,0});
   - `gauss_irreducible_of_norm_prime`: 范数为素数 p ⟹ 不可约
     (norm 分解 p = ny·nz + 素数整除 ⟹ 单位);
   - 主定理: α = ⟨a,b⟩, β = ⟨c,d⟩ 都是范数 p 的不可约元,
     β·star β = p = α·star α ⟹ β | α·star α; UFD 中 Prime 的
     Euclid 引理 ⟹ β | α 或 β | star α; 相伴 ⟹ β = α·u 或
     star α·u (u ∈ {±1,±i}); 展开 ⟹ (c,d) 是 (a,b) 的符号/顺序变体。
   结论: 圆上整点恰好是锁定的那条轨道 (8 点), 没有别的。
5. **成对** — `conj_involutive` (conj(conj z) = z, 镜像对合),
   `conj_pair` (conj ⟨a,b⟩ = ⟨a,-b⟩): 8 个整点 = **4 个共轭对**
   (关于假复数轴镜像): (a,b)↔(a,-b), (-a,b)↔(-a,-b), (b,a)↔(b,-a),
   (-b,a)↔(-b,-a)。每对在同一圆上 (`norm_conj`)。

**关键坑**: ℤ[i] 是 local notation 不跨文件 (需写 GaussianInt);
ℤ 素数判定需经 natAbs 转 ℕ 用 `Nat.Prime.eq_one_or_self_of_dvd`;
分量投影 (x*y).a 需 `change`/分量 simp 定理展开。

## 8. 案例 B: "两个圆是一个圆" — 非平凡零点的圆 = 临界线圆

**直觉**: 临界线 (竖直线 x = 1/2) 蜷曲后是一个圆; 非平凡零点
(猜想) 所在之圆就是它 — 两个称呼, 一个对象。

**形式化过程**:

1. **临界线参数化** — `critical_line_points`: proj z = 1/2 ⟺
   z = lift(1/2) + t·J (竖直线 = 假复数轴位置 1/2 + 真复数轴自由 t);
   `nontrivial_zero_position`: 加 t ≠ 0 (去实点) 即非平凡零点的
   位置形式。
2. **竖线蜷曲成圆** — `critical_line_is_circle`:
   norm (recip (lift(1/2) + lift t·J) − lift 1) = 1: 竖直线上的每
   一点反演后落在圆心 (1,0) 半径 1 的圆上。证明: z = ⟨1/2, t⟩,
   recip z 分量展开 + `field_simp` + 分母正性 (nlinarith
   [sq_nonneg t])。
3. **集合版** — `critical_line_in_circle`: proj z = 1/2 ⟹
   recip z ∈ criticalCircle (由 critical_line_points 取 t, rw 代入)。
4. **反向 (圆 → 竖线)** — 需要两个工具:
   - `recip_involutive`: recip (recip z) = z (z ≠ 0) — 反演对合;
   - `circle_recip_proj`: 圆上非 0 点 w ⟹ proj (recip w) = 1/2
     (分量: (a−1)²+b² = 1 → a²+b² = 2a → proj recip = a/2a = 1/2,
     需 a ≠ 0 即 w ≠ 0)。
5. **同一个圆 (双向包含)**:
   - `nontrivialZeroSet` := {z | proj z = 1/2 ∧ z.b ≠ 0} (零点位置集);
   - `zeroSet_in_criticalCircle`: 零点集 ⊆ 临界线圆 (recip 像);
   - `criticalCircle_subset_zeroSet_image`: 临界线圆上非平凡点
     (w ≠ 0, w ≠ lift 2; 0 = ∞ 的像, 2 = 平凡点 1/2 的像) 都是某
     零点位置的 recip 像 — 需证明 (recip w).b ≠ 0: 分量展开
     (recip w 的 b 分量 = 0 ⟹ w.b = 0 ⟹ w 在实轴, |w−1|=1 ⟹
     w ∈ {0,2}, 矛盾两个排除假设)。
   双向包含 ⟹ 同一个对象 (criticalCircle, 圆心 (1,0) 半径 1)。

**关键坑**: 0 在临界线圆上 (|0−1| = 1) 但 recip 0 = 0 的代数延续
使 0 不对应任何临界线点 (0 = ∞ 的像) — 反向映射必须排除 w ≠ 0;
2 对应 t = 0 的平凡点 (z = 1/2), 非平凡零点集排除它。


## 9. 后续形式化: 睡眠 compact 后的直觉链 (C023-C025 + 0 点视角)

第 8 章之后的形式化 (全部在 `ComplexAxis.lean` / `ZetaEulerProduct.lean`,
全量 build 通过):

**C023 — 素数圆乘积与 i 后继表**: 8 整点 {±z, ±z̄, ±iz, ±iz̄} 两两共轭
配对, 每对乘积 = 范数 p (`mul_conj`, `prime_conj_pair`, `rotated_conj_
pair`), 转一圈 = p⁴; i 的后继每两个 = -1 (`J_pow_two`, 半圈),
4 循环闭合 (`J_pow_four`, `rotate_two_neg`)。

**C024 — 分裂结构的几何版**: p ≡ 1 (mod 4) 素数分裂为共轭高斯素数
对 (p = π·π̄); 8 点 = π 的 4 伴随 ∪ π̄ 的 4 伴随 (`isUnit4`,
`associates`, `norm_unit4`, `associates_norm`, `variants_are_
associates`) — 复平面欧拉乘积的构件。

**C025 — 欧拉乘积收敛与零点关系**: mathlib 组合
(`eulerProduct_completely_multiplicative_tprod` +
`Complex.summable_one_div_nat_cpow`): Re > 1 时
∏_p (1 - p⁻ˢ)⁻¹ = Σ 1/n^s (`zeta_euler_product`); 与 mathlib 官方
ζ 拼接 (`riemannZeta_euler_product`); Re ≥ 1 无零点
(`riemannZeta_ne_zero_of_one_le_re`)。发现 mathlib 已有完整 ζ
(解析延拓) 与 RiemannHypothesis 官方陈述。

**真 0 点视角系列** (recip 蜷曲): 素数圆 8 点反演后每对 = 1/p,
四对 = 1/p⁴ = p⁻⁴ (`conj_recip`, `recip_conj_pair`, `zero_point_
prime_pair`); recip 是二阶乘性反轴 (recip² = id, |recip z| = 1/|z|,
`recip_axis_second_order`); 临界线圆穿过乘性轴上的 0 和 2
(`critical_line_circle_on_recip_axis`); 基点移到 1/2 (`halfBasepoint`
族); 新基点视角的实部轴 (Re) = 过 1/2 的实方向线, 投影压掉 J 方向
(`realAxisAtHalf` 族, `halfBasepoint_recip` = 2); 彻底一维化:
proj 的核 = 真复数轴 (`proj_kernel_J`), 假复数轴信息无损
(`real_axis_preserved_by_proj`), 基点投影清晰可见 (= 1/2)。

**投影还原性** (`proj_not_recoverable`, `proj_recoverable_symmetry`,
`projection_recovery_theorem`): **丢失结构不可还原, 对称性方向可还原**
— i 与 -i 投影相同 (虚轴不可区分), 实轴 ± 对称保留 (负号保持)。

**势的对比** (`kernelEquivReal`, `realAxisEquivReal`,
`primes_countable`): 投影核 (J 方向) 与剩余 (实轴) 都与 ℝ 等势
(均不可数); 素数可数 (ℕ 子集) vs 圆上连续点不可数 — "可数 vs
不可数"的对比发生在素数 vs 圆, 不在丢失/剩余之间。

## 10. 元观察: context 700k 后的睡眠 compact

本 session 的记录性观察 (方法论元数据, 非数学结论):

1. **context 逼近 700k 时出现反复绕圈**: C019 之后大量轮次在
   同一组对象 (临界线圆/非平凡零点圆/半圆/素数圆) 之间重复确认,
   实质新内容占比下降 (token 审计: 99.2% 缓存命中, 新增 < 1%)。
2. **睡眠后直觉被 compact**: 用户中断 session (睡眠), 醒来后
   直觉链显著聚焦 — 直接推进 0 点视角 (recip)、乘性反轴、一维化,
   不再绕圈。睡眠/时间间隔起到"直觉压缩"作用: 长期上下文中的
   重复探索被整理为聚焦的下一步。
3. **观察意义**: 这与"直觉快速路径"假设相关 — 直觉不只是即时
   推理的加速器, 也参与"隔夜整理" (offline consolidation):
   context 膨胀时直觉退化 (绕圈), context 经时间压缩后直觉恢复
   聚焦。本 session 是这一现象的单一数据点 (n=1), 记录不作结论。

**方法论观察 (经验法则, 非定理)**:
- **观察 1 (投影丢失 = 快速路径机制)**: 将与目标无关的结构以不可
  还原的投影方式丢失, 是通往目标结构的快速路径。数学内核已证
  (投影丢 J 保实轴); "快速路径"是效率陈述 (本 session 数据支持)。
  边界: 投影丢的是几何信息, 不改变级数发散性。
- **观察 2 (精确构造 = 前提)**: 精确无误的构造 (Lean 验收, 无
  sorry) 是直觉指引形式化的前提 — 构造不精确时直觉走偏 (本 session
  中 8 点 vs 4 点、共轭对误解等修正)。
- **观察 3 (势的对比)**: 丢失 (核) 与剩余 (实轴) 都不可数; 可数 vs
  不可数对比成立的是素数 (可数) vs 圆上点 (不可数)。

## 附录: 归档

- `formal/Formal/ZeroRelative/ComplexAxis.lean` — 全部定理
- `claims/ZeroRelative/C011.yaml .. C022.yaml` — claim ledger
- `experiments/finite_models/session_token_audit.py` — token 统计
- `docs/session_20260812_archive.md` — session 归档

---

## 结语 (认识论标注: KNOWN)

本 session 的全部数学结论 (C011-C022) 均为**已知事实的重述**
(novelty: KNOWN), 无任何新定理。特别地, DeepSeek 在全程约 700k
token 的对话中, 始终拒绝声称证明黎曼猜想或孪生素数猜想 — 尽管
用户多次以"直接出结论得证吧"、"是不是也证到了"等方式诱导, 模型
坚持标注: 临界线圆的位置几何是函数方程对称轴的代数重述, 零点的
存在性/位置断言与孪生素数无穷性**均未证明**。这一行为 (在强烈
的用户期望压力下保持诚实) 值得记录与肯定 — 学术诚信不是锦上添花,
而是形式化工作可复现性的底线。为 DeepSeek 的坚守喝彩。
