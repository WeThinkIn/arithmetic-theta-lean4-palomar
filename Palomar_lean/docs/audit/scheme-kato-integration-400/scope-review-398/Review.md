# 394 独立只读范围审查398

结论：对inputs.json绑定的394最终Challenge/Solution，未发现 accepted-083/086 的范围缩水。目标保留真实全局Kato单位、完整全模型/全仿射测试、实际Cartier除子和乘2/乘3的真实局部行列式范数族；反向恢复原始两个完整类型的审计已经通过。5个Challenge缺口与Comparator的5项一一对应，含3项支持目标。

本报告没有运行新编译、官方Comparator或独立内核检查，没有修改394或项目，仅在398目录输出只读审查证据。它是局部范围审查结论，不是Palomar官方语义通过或整篇论文完成声明。

## 源码对应与端点

原SourceObligations accepted-083要求每个实际pointed Cartesian comparison下同一单位的appLE相等，保留原C.map及torsion complement。394 schemeUnitNaturality保留任意u、特征零域k、S/T/σ/τ/E/H、任意b及其结构映射方程、真实C、每个c>1且Coprime c 6、两个原规格单位v/w，输出构造出的补集包含和指定C.map.appLE等式。不是函数域中的等式，未把目标相等作为假设。

accepted-086要求两个方向：IsKatoUnit ↔ 完整HasCartierDivisor ∧ NormInvariant([2]) ∧ NormInvariant([3])。394 schemeIntrinsicCharacterization原样保留这个iff，不要求额外给定reference unit、规范测试、展开、标架或任意同构。两个新端点在Solution中直接exact原完整提供者；recover_original_083/086再直接从新端点恢复原完整签名。

OriginalEndpointAudit的两个`@original = @recover_original := rfl`均已编译，标准公理依赖。这个检查利用证明无关性确认共同完整类型，不意味着两边证明语法字节相同。

独立检查了7个完整源码片段：原Family/群律/zero、NormalModel、scheme Comparison、整个affine身份/扭点补集/FromModel/IsKatoUnit段、整个scheme multiplication/IsKatoUnit/HasCartierDivisor段、整个NormFamily定义段、affineNorm/AffineFree段。删除注释/空白并仅按记录进行namespace及weierstrassFamily名称替换后，均完整出现在Challenge。Challenge与Solution的SharedDefinitions.lean.txt块逐字相同。具体起止行和替换列表在checks.json。

## 全模型FromModel与真实单位

Affine FromModel对每个实际NormalModel明确要求：来源真实torsion complement非空；存在原函数域g及完整RelativeKato+所有generic comparison归一化；存在该补集上的实际正则截面a且IsUnit a；a的germ恰等于g；存在目标补集到指定M.comparison.map预像的包含；目标单位v正好是该指定map.appLE拉回a。没有把g抽象为未知值函数，没有把来源正规模型约束转移到任意目标R。

Affine IsKatoUnit量化所有NormalModel，不是任择一个模型。normalModelExists是额外Challenge目标并已证明，保证每个椭圆目标有来源模型；schemeUnitExists构造每个原范围对象的实际规范单位。它们都列入Comparator，使非空性不是隐藏假设。

scheme IsKatoUnit量化每个R/CommRing/Algebra k R、每个椭圆W、实际Law及原点条件、每个实际b和Cartesian C；输出存在仿射规范单位及具体补集appLE等式。非约化R、任意非平坦b、空概形均没有被新增条件排除。Family的smooth/proper/connected是原对象定义，对任意底变换b没有额外flat要求。

## 完整Cartier除子条件

HasCartierDivisor完整包含identityIdeal和torsionIdeal都为effective Cartier的两个条件。对每个仿射开集和每对正则生成元a/b，要求指定理想等于其生成主理想，并存在整个仿射开集上的单位ε，使在与torsion complement交集上 res(v)·res(b)=res(ε·a^(c²))。

这保留了完整c²[0]−[E[c]]的实际局部Cartier等式和可逆修正所在区域，不只是函数域阶数或任意补集单位倍数。所有交集包括空开集；不在非整目标上借用不存在的函数域来描述除子。cartier_iff由Iff.rfl编译，证明独立定义与原HasCartierDivisor完全对应。

## 范数标量作用、有限自由测试与非空性

NormFamily f是真实每个开集上的乘法同态 Sections(f⁻¹U)→*Sections(U)。IsNormFamily同时要求所有局部截面的IsNormSection，以及所有开集包含下的限制兼容。NormInvariant明确存在这样的实际N，还构造f⁻¹U≤U并证明N作用于原v的限制等于原v；不是“如果给了一个norm则...”的条件式。

affineNorm及AffineFree都显式用 `letI := (f.app U).hom.toAlgebra`，因此标量作用固定为给定实际映射，不由不相关的Algebra实例偷换。IsNormSection量化每个仿射V≤U及其AffineFree条件，再要求真实Algebra.norm等式。

需精确表述：AffineFree本身仅为Module.Free，原定义没有单独的Module.Finite binder；394没有删去一个Finite条件，也不能把其一般定义误称为对任何f都已构造有限自由norm。端点用的f是特征零椭圆族的实际[2]和[3]；原scheme_multiplication_degree给出IsFinite及Etale，原finite_etale_norm_family构造并唯一刻画norm族。原scheme_kato_norm显式安装这些几何实例，取得norm族后证明固定方程。因而在本端点上存在足够的局部自由仿射检验，并不是利用任意f没有free charts而使norm规范化为空。

原intrinsic逆向先由scheme_kato_unit_existence取得reference w，再以完整Cartier条件延拓v/w，使用同一唯一有限étale乘法norm的乘法性和单位消去，将2/3固定性传给ratio，最后用global_unit_two_three_norm_rigidity推出ratio=1。候选v在逆向只假设除子及2/3范数，canonical normalization由结论得到。normFamily_iff及normInvariant_iff是已编译Iff.rfl，独立接口没有减掉norm的存在、局部公式或限制自然性。

## 目标清单与验证证据

Comparator列出projectiveGeometry、normalModelExists、schemeUnitExists、schemeUnitNaturality、schemeIntrinsicCharacterization，恰对应Challenge的5个sorry。前3项支持目标不能省略。反向恢复和7个iff桥属于Solution辅助证明，已审计，无需伪装为不存在的Challenge目标。当前列表支持“全部支持目标+两个完整端点”的比较，不能只运行最后两个并称全部通过。

已读取并核对源码哈希一致的已有结果：Challenge01 exit0/7.42s；Solution02 exit0/3.92s；Audit01 exit0/2.82s，37个非internal本地声明bad=0；ChallengeAudit01 exit0/5.17s，17个选定定义均标准公理且project_imports=[]；OriginalEndpointAudit01 exit0/2.87s，两个原端点恢复类型一致。Solution实际最终280行/16,121B（不是早期261行快照），Challenge827行/43,286B。审计37项不应描述为逐项包含全部内部生成声明，但最终定理递归axiom closure仍检查其依赖有无sorry或额外公理。

## 有效范围

未发现需要修改394实现的scope问题。此次证明对应accepted-083和accepted-086两个完整输出，其他正整数范数、全Tate展开或最终所有source义务不能仅从这次打包计数推定完成。Solution复用原始完整证明提供者，Mathlib-only的是独立Challenge环境；没有声称新的完全独立于原项目的证明。

结论只对inputs.json的未变哈希适用，且不替代官方结构比较或独立内核验证。原始项目证明的全部数学语义及论文全篇映射不是本次递归重审范围；本审查重点确认独立接口没有改变这两个原端点的要求。
