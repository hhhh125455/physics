# 物理推导 ↔ 数学结论 ↔ Lean 定理 ↔ 人类推导

## 使用方法

- 看论文版本：[`paper_zh.tex`](paper_zh.tex)。
- 看无实质性省略的已验证部分：[`detailed_zh.tex`](detailed_zh.tex)。
- 检查机器证明：[`ClassicalSpinKrylov.lean`](../ClassicalSpinKrylov.lean) 和 [GitHub Actions](../actions)。
- 每次更新相关 Lean 定理，都要同步修改详细推导；CI 使用 `scripts/check_traceability.py` 做基本的一致性检查。它**不能证明自然语言翻译忠实**，仍须逐步审阅。

| 编号 | 数学环节 | Lean 定理 | 人类推导 | 验证边界 |
|---|---|---|---|---|
| M1 | 偶数次幂积分 | `even_power_integral` | 详细版 M1 | 实际积分，CI 构建 |
| M2 | 加权积分闭式 | `spin_weight_integral` | 详细版 M2 | 实际积分，CI 构建 |
| M3 | 任意阶偶数矩 | `evenMoment_formula` | 详细版 M3 | 自积分定义得出 |
| M4 | 归一化、二阶、四阶矩 | `moment_normalized`, `moment_two`, `moment_four` | 详细版 M4 | M3 的推论 |
| L1 | 二阶、四阶矩与候选系数一致 | `fourth_moment_identity`, `second_lanczos_identity` | 详细版 §5 | **仅代数一致性** |

## 尚未 Lean 验证

- P1：泊松结构、哈密顿方程和 (S_x(t)) 的数学形式化
- P2：球面测度、方位角积分和 (C(t)) 的三角函数闭式
- P3：Liouville 算符的 Krylov 基定义与矩—Lanczos 恒等式
- P4：Gegenbauer 正交性与**全部** (b_n) 通项

**重要区别：** 即使所有已有定理在 CI 中通过，也只能表示 **M1–M4 和 L1** 的准确断言获 Lean 接受；无法据此宣布 P1–P4 被证明。

## 当前假设

(S>0)，(chiinmathbb R)，(c=2chi S)，(-1le zle1)；
对已验证的积分命题只要求 (cinmathbb R) 且 (ninmathbb N)。
计算 (b_2^2=(mu_4-mu_2^2)/mu_2) 时额外要求 (c
e0)。
