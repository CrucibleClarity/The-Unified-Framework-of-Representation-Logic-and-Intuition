# 阶段成果 hash 台账 (隔离文件, 2026-08-21 建立, 带时间戳)

> 每个隔离文件 = 独立编译通过 (0 error 0 sorry) 的阶段成果。时间 = 文件最后修改 (mtime)。
> 合并入 proof.lean 后原文件保留, hash+时间在此台账留存。合并文件 hash 见 claims_manifest.md。

| 时间 (mtime) | 文件 | hash (SHA256 前16) | 对应 claim/观测 | 状态 |
|---|---|---|---|---|
| 2026-08-21 09:19:28 | zeta_int_layer_iso.lean | 034508c228ad7d03 | C031+C032 / 观测 AO+AQ | 已合并 |
| 2026-08-21 09:14:25 | zeta_error_seq_iso.lean | 2fe7cc8c3fac1993 | T6f / 观测 AP | 已合并 |
| 2026-08-21 08:54:43 | zeta_phase_align_iso.lean | cce174d53529dd6f | C030 / 观测 AN | 已合并 |
| 2026-08-21 08:31:10 | zeta_axis_iso.lean | ea175a12ed383023 | C029 附 (0pat 自包含) | 已合并 |
| 2026-08-21 08:16:12 | zeta_lift_iso.lean | 079a295f8a517a69 | C029 / 观测 AM | 已合并 |
| 2026-08-21 08:03:42 | zeta_u_continuous_iso.lean | 91ee1b0f2795c5db | C029 / 观测 AM | 已合并 |
| 2026-08-21 07:56:35 | zeta_flip_iso.lean | 4a79928bb38ea45b | C029 / 观测 AM | 已合并 |
| 2026-08-21 07:34:18 | zeta_unit_sq_iso.lean | a58df5962a4205e7 | C028 / 观测 AL | 已合并 |
| 2026-08-21 07:21:24 | zeta_chi_translation_iso.lean | df7ba0f9387f124e | C028 / 观测 AL | 已合并 |
| 2026-08-21 06:16:18 | zeta_gamma_reduce_iso.lean | 3076f8d886a15ec4 | C026 / 观测 AI | 已合并 |
| 2026-08-21 06:02:18 | zeta_gamma_doubling_iso.lean | f1bae3b121404665 | C026 / 观测 AI | 已合并 |
| 2026-08-21 05:57:59 | zeta_term_phase_iso.lean | 6e9ef1c654c1e3da | 待标注 | 已合并 |
| 2026-08-21 05:53:39 | zeta_gamma_symmetry_iso.lean | 9b0b310ad80085b1 | C026 / 观测 AJ | 已合并 |
| 2026-08-21 05:45:49 | zeta_chi_explicit_iso.lean | b906c9ef39537e3f | 待标注 | 已合并 |
| 2026-08-21 05:31:16 | zeta_basepoint_i_circle_iso.lean | a1576f89e52064e1 | 观测 (i 圆) | 已合并 |
| 2026-08-21 05:11:00 | zeta_basepoint_one_iso.lean | e3ab009f5b7c3f66 | T2 (离线零点) | 已合并 |
| 2026-08-21 05:07:31 | zeta_basepoint_iso.lean | 9942a4ae37c01179 | T1/T2 (等价框架) | 已合并 |
| 2026-08-21 04:54:37 | zeta_euler_circle_iso.lean | e4e0c3c788078b66 | 待标注 | 已合并 |
| 2026-08-21 04:50:31 | zeta_zero_region_iso.lean | 75e28a2a4c47fd22 | 待标注 | 已合并 |
| 2026-08-21 04:49:12 | zeta_odd_even_iso.lean | 52c9b61c05289509 | 待标注 | 已合并 |
| 2026-08-21 04:30:59 | zeta_split_iso.lean | 406d981c175f9538 | 待标注 | 已合并 |
| 2026-08-21 03:26:29 | zeta_strip_iso.lean | 3931178d60b1a2b0 | 待标注 | 已合并 |
| 2026-08-21 (当前) | proof.lean (合并总, 215 声明) | 098dbee271e6b853 | 全部 | 当前 |
| 2026-08-21 (当前) | observation.md (观测 AM-AQ) | 388f0fc4e4ae0182 | 全部 | 当前 |

| 2026-08-21 10:06 | zeta_zero_order_iso.lean | 0f57bf3f5e931412 | T6h 零点阶 v1 (左右极限) | 隔离 |
| 2026-08-21 (当前) | zeta_zero_order_iso.lean | ad40314e738eb291 | T6h v2 + 翻转比值 (乘除法对消, 反射对称) | 隔离 |
| 2026-08-21 (当前) | zeta_argument_iso.lean | a27dcfd2bab9a658 | T6j 参数原理 (单零点, 对消积分形式) | 隔离 |
| 2026-08-21 10:06 | zeta_stirling_iso.lean | 581010a30921f455 | T6i Stirling 第一层 (乘子自反+模恒1) | 隔离 |
| 2026-08-21 (当前) | zeta_e_pi_i_bridge_iso.lean | fe17c58a083fe007 | T6k e^{iπ} 桥接 (e^{iπS}=u + 共轭奇性 S(-T)=-S(T)) | 隔离 |
## 记录纪律 (2026-08-21 用户要求)

- 每个新隔离文件编译通过后: 立即记录 hash + 时间戳到本台账 (含对应 claim/观测)
- 合并后: 更新 proof.lean/observation.md 的 hash 行
- 阶段成果 hash 与合并文件 hash 分离保留, 可独立追溯
| 2026-08-19 | zeta_stirling_iso.lean | 01bed96962535c5e | Stirling 模分量: log|Γ(1/2+it)| = (1/2)(log π - log cosh πt) + 渐近主项 |
| 2026-08-19 | zeta_stirling_iso.lean | d3b1816d81ee7cc4 | Stirling 第二层(桥): e^{iθ_χ}=χ 桥 + sin 相位精确 arctan(tanh) → π/4 |
| 2026-08-19 | proof.lean | 86ac6ae07ff4cc7e | 矩形闭合桥: 翻转计数 = χ 圈数 - 整数层 (flip_count_from_theta_lifts) + net_flip 修复 |
| 2026-08-19 | zeta_e_pi_i_bridge_iso.lean | bdc6df74806f8ecf | 增长控制落点: Sfunc_le_log (|S|≤1 ⟹ O(log T)) |

| 2026-08-21 | Zenodo | 10.5281/zenodo.22038154 | cpp_submission_0pat_riemann_unified 38 文件 (4 任务全部 0-sorry) |
| 2026-08-19 | zeta_zero_order_iso.lean | e95377476a7897da | 翻转=π跳桥: flip_phase_jump_pi/exp (翻转⟹u⁻/u⁺=-1=e^{iπ}) |
| 2026-08-19 | proof.lean | 8e574d945689f507 | 矩形闭合骨架: Λ₀反射对消 log∈2πiℤ + Λ₀零点等价 |
| 2026-08-19 | proof.lean | cf01a4515387afac | 卷已知曲线: ζ(2+it)有界(级数) + Γ(1+it)≤1(积分表示) |
| 2026-08-19 | proof.lean | 792cff814fcb8d9e | 底边拼装: 无零点(假实轴) + arg跳=π + ζ实轴实值 + ζ(-1)<0 |
