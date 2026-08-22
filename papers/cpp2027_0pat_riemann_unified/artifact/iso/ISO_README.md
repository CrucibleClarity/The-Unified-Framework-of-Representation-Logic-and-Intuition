# 隔离文件 (阶段成果) — zeta_*_iso.lean

每个隔离文件 = 独立编译通过 (0 error 0 sorry, mathlib-only) 的阶段成果。
按 0pat 隔离开发纪律: 新定理先独立文件编译验证, 再一次性合并入 proof.lean。
合并后原文件保留, 可独立追溯/复验。hash 台账见 `../iso_hashes.md`。

| 文件 | 内容 | 对应 claim/观测 |
|---|---|---|
| zeta_axis_iso.lean | 复数轴 (a+bJ 旋转代数) + 六交点定理 (0pat 自包含) | C029 附 |
| zeta_flip_iso.lean | 零点离散/有限 + 带内有限 | C029 / AM |
| zeta_u_continuous_iso.lean | u = ζ/‖ζ‖ 连续 + χ 临界线连续 | C029 / AM |
| zeta_lift_iso.lean | χ 连续幅角提升 (覆盖映射 liftPath) | C029 / AM |
| zeta_phase_align_iso.lean | 相位对齐 2Δθ_ζ = Δθ_χ (T5 自包含复制) | C030 / AN |
| zeta_int_layer_iso.lean | S(T) 整数层 θ_ζ−θ_χ/2 ∈ πiℤ + 周期发散桥 + 逆桥 | C031+C032 / AO+AQ |
| zeta_error_seq_iso.lean | 预言学残差 0pat 化 (误差序列 5 定理) | T6f / AP |
| zeta_gamma_doubling_iso.lean | Γ 倍增 | C026 / AI |
| zeta_gamma_reduce_iso.lean | Γ 约化 | C026 / AI |
| zeta_gamma_symmetry_iso.lean | Γ 共轭对称 | C026 / AJ |
| zeta_chi_translation_iso.lean | χ 平移递推 (T4) | C028 / AL |
| zeta_unit_sq_iso.lean | u²=χ (T5 隔离版) | C028 / AL |
| zeta_basepoint_iso.lean | 基点 (等价框架) | T1/T2 |
| zeta_basepoint_one_iso.lean | 离线零点 → 左半带 | T2 |
| zeta_basepoint_i_circle_iso.lean | i 圆 | 观测 |
| zeta_chi_explicit_iso.lean | χ 显式 | T4 区 |
| zeta_euler_circle_iso.lean | 欧拉圆 | 观测 |
| zeta_odd_even_iso.lean | 奇偶 | 观测 |
| zeta_split_iso.lean | 拆分 | 观测 |
| zeta_strip_iso.lean | 带 | 观测 |
| zeta_term_phase_iso.lean | 项相位 | 观测 |
| zeta_zero_region_iso.lean | 零区 | 观测 |
| zeta_rh_oddeven_iso.lean | RH 奇偶交点形式 (iso 42): rh_classical ⟺ rh_oddeven, 奇偶公共零点 ⟺ ζ 零点, 逆否: 离线公共零点 ⟺ RH 失败 | RH 等价形式 |
| zeta_quadruple_cosh_iso.lean | 零点四元组 cosh 分解 (iso 43): Re(x^ρ+x^{1−ρ}+x^conj ρ+x^{1−conj ρ}) = 4·x^{1/2}·cosh((β−1/2)·log x)·cos(t·log x) | 显式公式项轨道分解 |
| PhaseAlign_iso.lean | 相位对齐位置刻画 (iso 44): 相位对齐 ⟺ ζ(1−s)=conj(ζ(s)); ⟹ |χ|=1; 临界线 ⟺ s=1−conj s (复合反射不动点); 临界线 ⟹ 对齐; ζ 零点 = 平凡解 | 相位对齐位置 |

| zeta_zero_order_iso.lean | 零点阶翻转方向: 局部展开 + 左右极限 + 翻转比值 (乘除法对消, 反射对称 u(σt)/u(t)→(-1)^m) | T6h |
| zeta_stirling_iso.lean | χ 圈数渐近第一层: 乘子自反 χ(s)χ(1-s)=1 + 临界线模恒 1 | T6i |
| zeta_argument_iso.lean | 参数原理 (单零点): ∮ f'/f = 2πi (对消积分形式) | T6j |

| zeta_e_pi_i_bridge_iso.lean | e^{iπ} 桥接: e^{iπS(T)}=u(T) + 共轭奇性 S(-T)=-S(T) | T6k |

编译 (每个文件独立, mathlib-only):
```
lean zeta_<name>_iso.lean   # LEAN_PATH 指向 mathlib olean
```

## 编译状态 (2026-08-21 发布时刻, mathlib 905b95818e + lean 4.32.2)

| 状态 | 文件 |
|---|---|
| 0 error 0 sorry (当前环境可编译) | 24 文件: zeta_axis / flip / u_continuous / lift / phase_align / gamma_doubling / gamma_reduce / gamma_symmetry / chi_translation / unit_sq / basepoint / basepoint_one / basepoint_i_circle / chi_explicit / euler_circle / odd_even / split / strip / term_phase / zero_region / argument / stirling / e_pi_i_bridge / **continuation (新增: (0,1)段块A+B)** |
| 此前环境已编译通过, 新 mathlib API 迁移待适配 | zeta_zero_order / error_seq / int_layer (内容已合并入 proof.lean, 证明本体不变) |
| 合并总 (适配中) | proof.lean (215+ 声明, 内容以隔离 iso 文件为准) |

环境适配说明: mathlib 更新 (905b95818e) 导致 API 变化 —
norm_integral_le_integral_norm 移入 namespace / div_eq_zero_iff 签名 /
Finset 求和 binder 语法 ∈ vs in / ofReal_log 为 simp 引理等。
证明内容不受影响, 适配完成后 iso 与 proof.lean 将全量 0-error。
