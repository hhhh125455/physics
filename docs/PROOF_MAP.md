# 物理推导 ↔ 数学结论 ↔ Lean 定理 ↔ 人类推导

## 使用方法

- 看论文版本：[`paper_zh.tex`](paper_zh.tex)。
- 看无实质性省略的已验证部分：[`detailed_zh.tex`](detailed_zh.tex)。
- 检查机器证明：[`ClassicalSpinKrylov.lean`](../ClassicalSpinKrylov.lean) 和 [GitHub Actions](../actions)。
- 每次更新相关 Lean 定理，都要同步修改详细推导；CI 使用 `scripts/check_traceability.py` 做基本的一致性检查。它**不能证明自然语言翻译忠实**，仍须逐步审阅。

| 编号 | 数学环节 | Lean 定理 | 人类推导 | 验证边界 |
|---|---|---|---|---|
| M1 | 偶数次幂积分 | `odd_power_neg_one`, `even_power_integral` | 详细版 M1 | 实际积分，CI 构建 |
| M2 | 加权积分闭式 | `spin_weight_integral` | 详细版 M2 | 实际积分，CI 构建 |
| M3 | 任意阶偶数矩 | `evenMoment_formula` | 详细版 M3 | 自积分定义得出 |
| M4 | 归一化、二阶、四阶矩 | `moment_normalized`, `moment_two`, `moment_four` | 详细版 M4 | M3 的推论 |
| L1 | 二阶、四阶矩与候选系数一致 | `fourth_moment_identity`, `second_lanczos_identity` | 详细版 §5 | **仅代数一致性** |

## D. 自旋动力学：逐项形式化

独立人类展开文件：[动力学逐步推导](dynamics_zh.tex)；Lean 源码：[Dynamics.lean](../ClassicalSpinKrylov/Dynamics.lean)。

| 编号 | 物理步骤 | Lean 对应定理 | 状态或边界 |
|---|---|---|---|
| D1 | 自旋泊松结构常数 | `bracket_xy`, `bracket_yz`, `bracket_zx`, `bracket_antisymm` | 点处梯度的泊松张量已验证；抽象 Poisson Jacobi 性未验证 |
| D2 | 哈密顿量对 z 求导 | `hamiltonian_z_derivative` | 实函数求导已验证 |
| D3 | 三条 Hamilton 方程 | `vectorField_x`, `vectorField_y`, `vectorField_z` | 由指定 Lie–Poisson 张量推导 |
| D4 | 长度和能量瞬时守恒 | `lengthSq_derivative_zero`, `energy_derivative_zero` | 已验证代数恒等式 |
| D5 | 候选轨道初值、z 不变 | `evolve_zero`, `evolve_z` | 轨道满足 ODE 还需微分验证 |
| D6 | 候选轨道保持长度及能量 | `planar_rotation_length`, `evolve_lengthSq`, `evolve_hamiltonian` | 旋转代数，不代表已经证明轨道满足 ODE |

| D7 | 显式轨道的实际时间导数 | `rotation_x_hasDerivAt`, `rotation_y_hasDerivAt`, `evolve_solves_x`, `evolve_solves_y`, `evolve_solves_z` | 必须由 Lean 检查后才能标记为已验证；见动力学 LaTeX §6 |

## 尚未 Lean 验证

- P1（剩余）：完整 Poisson 代数 Jacobi 结构；显式轨道满足 Hamilton ODE 的逐分量证明见 D7
- P2：球面测度、方位角积分和 (C(t)) 的三角函数闭式
- P3：Liouville 算符的 Krylov 基定义与矩—Lanczos 恒等式
- P4：Gegenbauer 正交性与**全部** (b_n) 通项

**重要区别：** 通过 CI 只意味着 **M1–M4、L1 和 D1–D7** 的准确断言获 Lean 接受；无法据此宣布整条物理证明链已完成。

## 当前假设

(S>0)，(chiinmathbb R)，(c=2chi S)，(-1le zle1)；
对已验证的积分命题只要求 (cinmathbb R) 且 (ninmathbb N)。
计算 (b_2^2=(mu_4-mu_2^2)/mu_2) 时额外要求 (c
e0)。
