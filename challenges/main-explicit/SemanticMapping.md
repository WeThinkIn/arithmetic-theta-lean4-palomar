# 主定理有限决定：独立 Challenge 草案

这是 Palomar 挑战规格，**不是已证明的 Solution，也不是全论文验证结果**。`Challenge.lean` 仅导入 Mathlib，156 行；唯一 `sorry` 位于待比较的主命题。Lean 类型检查退出 0，日志只有预期的 `declaration uses sorry` 警告。未调用官方预检、Comparator 或提交接口。原 13 项要求、103 个端点全部保留，见 `ScopeLedger.json`。

## 数学对象和精确结论

对任意自然数秩 n、任意非空有限族 h>0，以及全部满足对称、整数、偶对角和正定条件的 Gram 矩阵 A_i，使用

- Q_i(x)=xᵀA_ix/2，x∈Zⁿ；第 a 个系数是**全部整数解** Q_i(x)=a 的数量。
- θ_i 为这些壳层计数给出的完整形式幂级数，T(c)=Σ_i c_i θ_i 是 C-线性映射。
- 首个结论要求每个实际壳层有限，避免 `Nat.card` 对无限类型返回 0 的歧义。
- M_B(a,i)=#{x∈Zⁿ:Q_i(x)=a}，0≤a≤B，首先视为 Q 矩阵，再经 Q→C 延标量；不是自由输入矩阵。

正交化使用确定的整数迭代：从 C=I 开始，对于第 k 列 b，把每个后续列 v 替换为 ⟨b,b⟩_A v−⟨b,v⟩_A b。最终 B_i 和 m_ij=⟨B_i e_j,B_i e_j⟩_A 均由 A_i 的有限整数运算定义。原证明负责证明其非退化、正偶性及 B_iᵀA_iB_i=diag(m_ij)，这些不被新增为输入假设。

余类是实际加法商 B_i⁻¹Zⁿ/Zⁿ。`Indexing` 的见证给出 |det B_i| 个代表，`Indexed` 要求它们到该商的映射双射。每个 m_ij t_j 模 m_ij 的余数 a 取于 Fin m_ij，再用

    centered(m,a) = a                 若 2a<m，
                    a−m              否则

选唯一中心化整数代表。`pair` 单射、每次出现必须命中 `pair`、每个 `pair` 必须实际出现，三者保证 s=`U.count` 恰为实际不同一元对 (m,ν) 的数量，不能随意增加 s 来掩盖更弱的界。

定义

    N = lcm_{i,j} m_ij,
    L = 24 N²,
    K = (1+12N)²−1,
    I(L) = L³ ∏_{p|L}(1−p⁻²),
    B_* = n K^s I(L)/48.

Lean 自然数 cutoff 采用 n K^s |SL₂(Z/LZ)| / 48；命题另行要求它与上述**有理数乘积式严格相等**。因此自然数整除取商不会偷偷替代该精确公式，群阶乘积恒等式及整除性必须由 Solution 的现有证明导出。

主结论存在 B，但其选择受到完整显式公式约束：n=0 必须 B=0；n>0 必须存在上述真实索引 U 且 B=cutoff(A,U)=(n K^s I(L))/48。对**每个 B'≥B** 同时要求

    ker_C T = ker_C M_{B'},
    T(c)=0 ↔ ∀a≤B', [q^a]T(c)=0.

秩零分支还要求 T(c)=C(Σ_i c_i)。没有满秩/线性无关假设，任意退化关系空间均保留；也没有给定几何实现、全局截面存在、局部到全局比较或未证明系数界作为前提。

## 与论文及 103 端点的映射

[论文 PDF](../../paper/Arithmetic%20determination%20of%20relations%20among%20lattice%20theta%20series%20-%20A%20formal%20Tate%20and%20finite-cover%20construction%20with%20Lean%20verification.pdf) 的 Input and the finite-coefficient theorem 一节给出实际 θ、零秩、N/L/K/s/I/B_* 和矩阵核。本包审计时核对的原始 LaTeX 快照及当时仓库快照的输入哈希保存在 receipt 中；仓库当前以 PDF 作为论文发布文件。

本包的主要证明入口是 accepted-037 `ArithmeticThetaConservativeKernelR0189.conservative_matrix_kernel`。其内部已调用 accepted-035 `arithmetic_geometric_family_existence` 和 accepted-036 `geometric_family_conservative_cutoff`；构造几何的责任仍在已接受原证明依赖链中。本 Challenge 不把这些存在结论改写为假设。原 theorem 额外返回 `FormalIdentity A U`；本包仅消费其精确索引和核结论，完整余类乘积恒等式仍须由单独 orthogonal factorization 包覆盖。

本包**不单独覆盖**原主定理的实际模形式族、所有扩域、模截面像基与坐标，也不覆盖全论文几何证明路线、精细界、停止证书和算例。accepted-088、conservative-image-consumer 和另外七个计划包仍需独立比较；不能把本包通过宣称为 main 要求或全论文全部完成。

## 定义相等与桥接清单

| 对象 | 当前独立定义与原实现的关系 | Solution 必须完成的工作 |
|---|---|---|
| validGram、theta、thetaMap | 定义体与 `ArithmeticThetaComputed` 相应定义一致；命名空间不同 | 建立可复用的 `rfl` 或 `change` 桥，并在当前版本核检查 |
| pairing/project/step/runPrefix/basisMatrix/norms/naturalNorms | 仅依赖 Mathlib 的确定性整数算法；定义体对应原 `OrthogonalAlgorithm` | 泛型定义桥原则上可由 `rfl` 证明，不能仅凭文本对照宣布已通过 |
| castVec/integerVectors/preimageLattice/periods/cosetClass/Representatives | 与原真实有理预像商的定义体一致 | 核验下层定义展开后的定义相等；保留具体商，不替换为任意有限类型 |
| commonN/centered | 与原 `LatticeGlobalSectionsDefinitionsR0188` 一致 | `rfl` 定义桥 |
| Indexing | 独立新 structure 与原 structure 是不同类型 | **不能** `rfl` 当作同一类型。显式逐字段构造新 U，运输 representatives/residue/count/pair/index；证明 Indexed 保留及 count 相等 |
| Indexed | 展开后同五组真实算术条件，但依赖不同 Indexing | 对逐字段转换后的 U 证明对应；下层定义相等后预期可 `change`/`simpa` |
| level/exponent/levelIndex | 与原 24N²、(1+12N)²−1、素因子乘积式一致 | 定义桥；levelIndex 并非群阶的定义别名 |
| cutoff | 群阶自然数公式相同，U 需转换 | count/commonN 的桥之后连接原 cutoff；精确有理公式消费原 accepted-037 的证明 |
| coefficientMatrix | **不定义相等**：Challenge 用真实壳层 Nat.card；原实现用 `coefficientsUpTo` 的可执行列表 | 应用 `computed_coefficient_matrix`/`coefficient_prefix_exact`，逐元证明 Q→C 后矩阵一致；不能 rfl 替换 |
| 壳层有限性 | 新命题额外显式表达原有效性基础 | `ArithmeticThetaLattice.exact_shell_finite n Q hQ a`，再用 Set.Finite 转成 subtype 的 Finite |
| 所有更大截断的核 | 原 accepted-037 已提供全部 B'≥B | 通过矩阵桥与 thetaMap 桥逐项运输 |
| 逐系数等价 | 由核结论加有限前缀线性映射解释得到 | `computed_prefix_map` 或独立有限和逐系数计算；Fin(B'+1) 与 a≤B' 的转换 |
| rank0 | 原 accepted-037 已给 T(c)=C(Σ c) | 定义桥后直接消费，不额外假定 |

本任务仅完成独立规格类型检查；上表 Solution 桥均未在本工作轨道中编译，不能把“预期定义相等”当作已检查结果。

## 建议接入顺序

1. 保留当前 pilot 配置，另外建立 main-explicit 配置；不要覆盖它的历史验证记录。
2. 在 Solution 中复刻同一独立数学命名空间，或按 Palomar 当前接口约束共享允许的声明布局；Solution 允许导入证明库，Challenge 不允许。
3. 先证明 definitions/indexing/actual-coefficient 三类桥，再用 accepted-037 组装全部结论，最后检查 Solution 主定理没有 sorry/custom axioms。
4. 与其余七个包共同维护全 103 端点覆盖表。私有仓库只做本地/内部检查；用户要求转公开后再进行官方预检和正式提交。
