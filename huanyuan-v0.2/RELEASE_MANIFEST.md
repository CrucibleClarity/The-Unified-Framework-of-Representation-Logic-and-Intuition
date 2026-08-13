# Huanyuan (幻元) Release Integrity Manifest — v0.2

> 生成: 2026-08-12 | 版本: v0.2 (论文资产 v2: EN+ZH 全量, 符号修复) (方案A: numeral → num 序列折叠, base-256)
> 用途: 锁定 release_v0.2/ 全部资产 SHA256, 供 GitHub 上传前校验。
> v0.2 核心: num_0..256 概念 + num_concat 算子 (方程 concat(a,b)=a×256+b) +
>           num_seq gtoken + fold_num_v5 权重 (225K 参数, 折叠 + 全任务判定 1.000).

## 资产清单 (SHA256)

### 权重与配置 (fold_num_v5, 225K 参数)

| 资产 | SHA256 | 说明 |
|---|---|---|
| `fold_num_v5_model_fp32.pt` | `4aff787ffd1416cfe581728ddd8d034c26d970b2ed4799950084c477e2dc4491` | fp32 (923,910B), 判定 1.000 |
| `fold_num_v5_model_int8.pt` | `7b7bb128eaf5d4d5fe551793e33ce97031c4f529a85e0ea16dfa9c206cee4324` | int8 QAT (253,385B, 3.65x), 判定 1.000 |
| `fold_num_v5_config.json` | `1a3a7c9826f8c615f1ac5fdc5357ff285cad06743509578e300bad2f15a76791` | |
| `fold_num_v5_metrics.json` | `03676660326ab5f920af50626a13d8f7000f14ed9d5a2ca5a02bd38d240d2aa1` | |

### token 数据 (含 num_0..256 + num_concat + num_seq)

| 资产 | SHA256 |
|---|---|
| `tokens/concept_token.jsonl` | `b46047cc0123c4c6a5ef09914f8c824023d45503ca3743820fdd94d908e930f5` |
| `tokens/baseloop.jsonl` | `916b3eed0e5e54de8b452bc69fd956b8bdf9b3bb462b8035e9624cb42103cbfe` |
| `tokens/arrow_tokens.jsonl` | `abf1ae612f12cc59e83cd1cdd5159175eef9e267e2e5b0f9ffb0d38f11cdb6e6` |
| `tokens/symbol_tokens.jsonl` | `4717ddb80b11214d484123ae63b704bc8eb2651faba82899ba18e0cd1f663793` |
| `tokens/grammar.jsonl` | `717ddba16732de285e8ffb9186e35a8bc88303d1efbae1b62eb700464f80c2b5` |
| `tokens/presentation.jsonl` | `a3603bba1115d5cc2e80ef39bf7b443bcb9c5e57deb248f675ce61ae2f367364` |
| `tokens/explain.jsonl` | `c4b7fb9aa5e85afa5a1621bffcbfa987e14db82c60364940ff0fe9ce57e054d5` |
| `tokens/itoken.jsonl` | `25afa8343fb8e2a879a5a6aecd0fdccb5ba21379f7a778cf8d97bd6d2a5a5cbd` |

### 公开文档

| 资产 | SHA256 |
|---|---|
| `脱敏摘要_可解释泛化.md` | `9b8aa17336e0a1c893837e5b01495899783c10c5396d1dbe5a7c83e0b5f29130` |
| `CITATION.cff` | `db114861687f5b9281f47583f4693c1fa01ac00fd974639bf78711e1283019fd` |

## v0.2 成果摘要

- **num 折叠**: numeral (digit 序列) → num_0..255 序列 (base-256, 高→低), 2000 位十进制 → 831 num token (2.4× 压缩)
- **num_concat 算子**: 方程 concat(a,b) = a×256 + b (law 采样 + direction_ops OOD 自动覆盖)
- **num_seq gtoken**: num 序列排列方法 (G:34), 相邻合并 ×256+后位
- **eval_op 方程求值**: num_concat(96,3)=24579, 回归 10+23=33 / 7*6=42 保持
- **fold_num_v5 权重**: 225K 参数, 判定 1.000, 全任务保持

## 校验方法

```bash
cd release_v0.2
sha256sum -c <(cat <<'EOF'
4aff787ffd1416cfe581728ddd8d034c26d970b2ed4799950084c477e2dc4491  fold_num_v5_model.pt
EOF
)
```

## GitHub 上传准备

- 上传内容: 全部 assets (权重 + token 数据 + 摘要 + cff)
- 经桥: `api.github.com` POST (release + assets)
- 鉴权: `GH_TOKEN` (需宿主注入)
- 注意: v0.2 尚未含完整论文 (论文仍锁定在 v0.1 层), 如需论文 PDF 上传单独确认

## paper_data (实验结果与配置, 2026-08-11 补充)

### 结果表与文档

| 资产 | SHA256 |
|---|---|
| `paper_data/results.csv` | `3ee3f7a17e9a52b72b650123485e3c96a1a7266b20eb02be4e4751a123e2648e` |
| `paper_data/exp*.md` (15 份结果文档) | 见各文件 (随包) |

### 配置 (paper_data/configs/, 37 个)

| 关键配置 | SHA256 |
|---|---|
| `paper_data/configs/fold_num_v5_int8.json` | `58b65d951905b996d595890c58741c7cecfb9ad3411bd0ca956afb524d6e816d` |

### 脚本 (paper_data/scripts/, 14 个)

复现指南: `paper_data/scripts/README.md`

## 模型双版本说明

- `fold_num_v5_model_fp32.pt`: fp32 原始权重 (923,910B), 判定口径 1.000
- `fold_num_v5_model_int8.pt`: int8 QAT 打包 (253,385B, 3.65x 压缩), 判定口径 1.000 (无损)
- int8 版本权重落在 int8 格点 (量化误差 0), 反量化后与 fp32 行为一致

## papers (论文资产, 2026-08-12 更新: EN+ZH 全量)

> 9 篇论文 × 3 格式 (md 源 / tex / pdf)。PDF 经 pandoc+tectonic 生成,
> 中文字体 Noto Sans CJK SC + DejaVu Sans (希腊/数学符号全覆盖, 0 missing)。
> 中文版为英文版之翻译 (双语标题, 结构/编号/术语一致)。

| 资产 | SHA256 | 说明 |
|---|---|---|
| `papers/Generalization_as_Formalized_Induction_Token-Native_Factorized_Representation_Weight_Compilation.md` | `76eb0a5f274eb82c24f16ec31a97334eb53e64e2fa5233f4da08a58531b79d1b` | P1 泛化作为归纳形式化 源 md |
| `papers/Generalization_as_Formalized_Induction_Token-Native_Factorized_Representation_Weight_Compilation.pdf` | `244d7116e240f32d16c0b3b7929bac85da9a3e5058a84303e03e20e156af4793` | P1 泛化作为归纳形式化 PDF |
| `papers/Generalization_as_Formalized_Induction_Token-Native_Factorized_Representation_Weight_Compilation.tex` | `c7ba9344165b96dd1e8a184e3b3bb8ededc2690a5899d2500ee9f125b19521df` | P1 泛化作为归纳形式化 TeX |
| `papers/Generalization_as_Formalized_Induction_Token-Native_Factorized_Representation_Weight_Compilation_ZH.md` | `90bfbf55a2791a53f894f5400a90d4d1c5a085a802847ed29c292003717ee963` | P1 泛化作为归纳形式化 (中文版) 源 md |
| `papers/Generalization_as_Formalized_Induction_Token-Native_Factorized_Representation_Weight_Compilation_ZH.pdf` | `8e06665b0611b961cc5873ac500e8488a7b776d496fb535dd4b4ce17a180be4c` | P1 泛化作为归纳形式化 (中文版) PDF |
| `papers/Generalization_as_Formalized_Induction_Token-Native_Factorized_Representation_Weight_Compilation_ZH.tex` | `0ea262b4ebbab2f105507036f4c738f26738eaf763387aee42a281aa59c8ecaa` | P1 泛化作为归纳形式化 (中文版) TeX |
| `papers/Neural_Macro_Compilation_Compiling_Slow_Construction_Paths_into_Fast_Reasoning_Paths.md` | `9c205000dc06f60b2dc14f2e7d3bbfe39261e0c74fd4b33b7a8635aed6949dea` | P2 神经宏编译 源 md |
| `papers/Neural_Macro_Compilation_Compiling_Slow_Construction_Paths_into_Fast_Reasoning_Paths.pdf` | `08eae0cd2f498979ec0f2296f0f5c494e3319fadec8220547e13999f24f4b8a7` | P2 神经宏编译 PDF |
| `papers/Neural_Macro_Compilation_Compiling_Slow_Construction_Paths_into_Fast_Reasoning_Paths.tex` | `7a4a5bc7f443fd44b907184401e0fb179a1222f9d5cf89e6e6ff9d0feb05e24f` | P2 神经宏编译 TeX |
| `papers/Neural_Macro_Compilation_Compiling_Slow_Construction_Paths_into_Fast_Reasoning_Paths_ZH.md` | `acef089488fd59324a14e986778adde3c602b7539671a1e4e1d4fa065a746d33` | P2 神经宏编译 (中文版) 源 md |
| `papers/Neural_Macro_Compilation_Compiling_Slow_Construction_Paths_into_Fast_Reasoning_Paths_ZH.pdf` | `78f36eede2953c7fa7cad2b7cf2b52cba8fdb69bc973604151a92b9d7d1c779a` | P2 神经宏编译 (中文版) PDF |
| `papers/Neural_Macro_Compilation_Compiling_Slow_Construction_Paths_into_Fast_Reasoning_Paths_ZH.tex` | `c160a2f470d7c09b09fd12defbf10160b71f4f4f3a1fe620d6d5594019cd0651` | P2 神经宏编译 (中文版) TeX |
| `papers/Three-Channel_Equivalence_Construction_Intuition_Formal_Rewriting.md` | `3f029b15d70732885b39f82cf4aeee1bc6c21a4b02d294e1eae176e88e961d9e` | P0 三通道等价 源 md |
| `papers/Three-Channel_Equivalence_Construction_Intuition_Formal_Rewriting.pdf` | `d21f434083f011e0e53a7e1146948e6e4e6eaeb5eeac39c7ebb979abc20eeffe` | P0 三通道等价 PDF |
| `papers/Three-Channel_Equivalence_Construction_Intuition_Formal_Rewriting.tex` | `b6e5f580542b6d63851415961badaa0d1a07c3f4b5b4a2b13f255f88082f0594` | P0 三通道等价 TeX |
| `papers/Three-Channel_Equivalence_Construction_Intuition_Formal_Rewriting_ZH.md` | `2016ee69ea94ca2a140f4d039fc3668656e176ab791ebedc8335f7428fe93ae5` | P0 三通道等价 (中文版) 源 md |
| `papers/Three-Channel_Equivalence_Construction_Intuition_Formal_Rewriting_ZH.pdf` | `ab8a44aecfa32738b3ecb60edb865ba1c61d982e22e5cb73d0d309edd69a4e2f` | P0 三通道等价 (中文版) PDF |
| `papers/Three-Channel_Equivalence_Construction_Intuition_Formal_Rewriting_ZH.tex` | `2320d44a652330e9f2cf99cc80d50aca728196835865eb63d584e88ac7097653` | P0 三通道等价 (中文版) TeX |
| `papers/arxiv/Intuition-Guided_Formalization_of_the_Riemann_Zeta_Direction_Projection_Prime-Circle_and_the_Worn-Zhe-Yue_Method.tex` | `a2fdeb813c9ac229408e57b4c94fb574f50e91c973a5dd229b1d1921167e1213` | 完整研究论文 arXiv 格式 LaTeX (thebibliography+MSC2020+提交元数据) |
| `papers/conjectures_packaged.md` | `a47adf302b4a4a35eb0e583731055d7b3e38b26e9e3396bea762b20a385ebdbf` | 猜想清单 (神经病猜想, v1.1 DOI 21901857) 源 md |
| `papers/conjectures_packaged.tex` | `387989c89208a3835f53c201c51c9c447fd3e49fff3fe93fca0baa39f6b58366` | 猜想清单 (v1.1) TeX |
| `papers/conjectures_packaged.pdf` | `0e0b10fe91011df737e3b40c5c030afe2bfb40556fb3b94c37b864dfe0c3e8f8` | 猜想清单 (v1.1) PDF (CJK 渲染) |
| `papers/Intuition-Guided_Formalization_of_the_Riemann_Zeta_Direction_Projection_Prime-Circle_and_the_Worn-Zhe-Yue_Method.md` | `c654f12a55b9fcae9404a40d9a6f6f0de840ac64e84aab7d690073c6cdbf42bb` | 完整研究论文 (21897167) 源 md |
| `papers/Intuition-Guided_Formalization_of_the_Riemann_Zeta_Direction_Projection_Prime-Circle_and_the_Worn-Zhe-Yue_Method.tex` | `384d94f05550f0e0acd9206cb67dda54fd1875c3c0cf3e399bf0d31e7bcd44cf` | 完整研究论文 (21897167) TeX |
| `papers/Intuition-Guided_Formalization_of_the_Riemann_Zeta_Direction_Projection_Prime-Circle_and_the_Worn-Zhe-Yue_Method.pdf` | `d26e8395742366f6d6ce12d0b74eb99885a6b7757b7db3457fb0c7ddadafb83b` | 完整研究论文 (21897167) PDF |
| `papers/Intuition-Guided_Formalization_of_the_Riemann_Zeta_Direction_Projection_Prime-Circle_and_the_Worn-Zhe-Yue_Method_ZH.md` | `ccec32ce4ad9f8ea03007bc114faa88554d9ca84fd1ddb57367049df82946446` | 完整研究论文 (21897167) (中文版) 源 md |
| `papers/Intuition-Guided_Formalization_of_the_Riemann_Zeta_Direction_Projection_Prime-Circle_and_the_Worn-Zhe-Yue_Method_ZH.tex` | `653454a073e23398ced3343fd714bee15aa2491062c9465830ba362469b24264` | 完整研究论文 (21897167) (中文版) TeX |
| `papers/Intuition-Guided_Formalization_of_the_Riemann_Zeta_Direction_Projection_Prime-Circle_and_the_Worn-Zhe-Yue_Method_ZH.pdf` | `fb6cfb15bba584ab2d7e799c8cfa708efe9d2c8d1bc3fa500c75caa012754eef` | 完整研究论文 (21897167) (中文版) PDF |
| `papers/Unified_Framework_Representation_Logic_Intuition.md` | `37d5fecedc671866385c572fd1b8cd1825322c48d212b6d19809e1faa86c0f73` | 纲领 (中文源) |
| `papers/Unified_Framework_Representation_Logic_Intuition.pdf` | `0ad152e7e2ade051d503f7db2ec747d7e30be0969ebe414edc47e49a336d4a3f` | 纲领 PDF (中文渲染) |
| `papers/Unified_Framework_Representation_Logic_Intuition.tex` | `605ea7a5e46a9f8c831cc18ec335e01322e75a2f3658048cc868bfbcb0b928f7` | 纲领 TeX |
| `papers/riemann_direction_formalization.md` | `d2ba0d50115afd8d50a39cdfaa2688189f131fe6cc7980c389c67baf23b7ce25` | 黎曼方向形式化主论文 源 md |
| `papers/riemann_direction_formalization.pdf` | `ebca126ebeca68fd3ba643f05ea0b97ad97aa06aeab899f0187aa211ea030f00` | 黎曼方向形式化主论文 PDF |
| `papers/riemann_direction_formalization.tex` | `e67a7d52a14ab0308b12f2cb6ed6c2141ac85521ebb7682566ee40613e018180` | 黎曼方向形式化主论文 TeX |
| `papers/riemann_direction_formalization_ZH.md` | `75b4be40a5dc52087f928637fe9a16313795a8cbd8309624555e81ca9664e9e4` | 黎曼方向形式化主论文 (中文版) 源 md |
| `papers/riemann_direction_formalization_ZH.pdf` | `0ada573e0d8dd640cad038daf3c12c9a59ed2ce61c0a1da3e81bd0f344881529` | 黎曼方向形式化主论文 (中文版) PDF |
| `papers/riemann_direction_formalization_ZH.tex` | `d2f0a85bd540b30865d2d17cdc32177cd51257922e00e376fdffda693981ce52` | 黎曼方向形式化主论文 (中文版) TeX |

## papers (新增: 基点相对性, 2026-08-12)

| 资产 | 说明 |
|---|---|
| `papers/basepoint_relative_stability.md/.pdf` | 基点相对性稳定与值域漂移 (C001-C010, 英文) |

与黎曼主论文 (C011-C025) 互补: 本论文覆盖代数基础 (heap 选基点恢复群/
位移空间/内生生成律), 黎曼论文覆盖分析方向 (投影/圆/欧拉乘积)。

## papers (更新, 2026-08-12)

| 资产 | 说明 |
|---|---|
| `papers/riemann_direction_formalization.md/.pdf/.tex` | 黎曼方向 (DOI 10.5281/zenodo.21896990; 穿折越方法 + 作者声明) |
| `papers/basepoint_relative_stability.md/.pdf` | 基点相对性稳定与值域漂移 (C001-C010) |

穿折越方法 (作者命名): 通过人为精确构造投影结构丢失, 将不可数问题的发散结构
剔除至人类数学空间之外, 以较低神经网络推理成本获得快速直觉路径。
作者坚称 (不代表 DeepSeek 意见): 基点构造诱导下的数学空间穿折越证明方法。

## papers (新增完整论文, 2026-08-12)

| 资产 | 说明 |
|---|---|
| `papers/riemann_projection_formalization_full.md/.pdf` | 完整研究论文 (DOI 10.5281/zenodo.21897167): 投影诱导结构丢失 + 穿折越方法; 含文献综述/完整证明展开/批判性讨论/参考文献 |

与 riemann_direction_formalization (技术记录, DOI 21896990) 的区别:
- 21896990: 形式化工作记录 (C011-C025)
- 21897167: 完整研究论文 (补 Related Work/References/证明展开/ζ衔接/批判性讨论/Future work)
