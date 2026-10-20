# 385 独立只读 scope review（391）

结论：在 inputs.json 绑定的385源码版本中，未发现 accepted-080/081 的目标范围缩水、任意比较同构替换、仅正常/约化测试或空归一化类造成的缺口。最终 scheme_exists / scheme_naturality 通过双向谓词桥和精确拉回桥对应原始两个完整端点；反向恢复定理也已编译。全部10个Challenge证明缺口均列入 comparator.json，没有仅提交最后两个端点而遗漏支持目标。

这是源码范围审查并结合已存在编译记录的结论，不是 Palomar 官方语义通过，不是整个论文或所有 SourceObligations 的完成证明。复核者没有运行新编译、导出或官方比较器，没有修改385或项目文件；只在391目录写入本报告、检查结果及哈希。

审查依据：project/docs/SourceObligations.json 的 accepted-080/081 完整 type 与 source_statement；项目的 LocalWeierstrassDefinitionsR0203、ArbitraryDiscriminantDefinitionsR0243、SchemeDiscriminantDefinitionsR0244、SchemeDiscriminantExistenceR0244、SchemeDiscriminantNaturalityR0244；385 Challenge、Solution、Comparator及已存在构建/审计输出。审查范围不是递归重新证明所有导入提供者。

## 1. 原始端点与最终输出

accepted-080 要求每个特征零域 k、任意 k 上概形 S、实际 Family S 都有一个真实恒等余切第24张量幂上的全局截面，并满足所有实际仿射 Weierstrass 测试。Challenge:965 的 scheme_exists 保留这些参数，没有要求预先给定截面、坐标、标架、正规覆盖或有限型底概形。

accepted-081 要求任意 S、T、b:T→S、结构映射方程及实际 pointed Cartesian Comparison，两个满足规格的截面满足真实拉回相等。Challenge:969 保留全部这些参数、hd/he条件及输出。hd/he 是原本端点就有的规范化条件，并非把要求证明的拉回相等当作假设。

Solution 的 scheme_iff_original 给出 SchemeSpecification ↔ 原始 SchemeDiscriminantR0244.IsD2；pull_eq_original 是完整全局截面上的拉回等式。scheme_exists 调用原始存在定理后使用 iff 的反向；scheme_naturality 使用原始自然性及同一 iff 的正向。recover_original_080/081 分别从新端点反向恢复原始完整签名。

已有 OriginalEndpointAudit 用两个 `example : @original = @recover_original := rfl` 验证原始端点与反向恢复定理可在同一完整类型上比较，并打印标准公理依赖。其 exit0 是实际编译结果。由于 Lean 的证明无关性，这里的 rfl 证据证明类型对应，不应解释为两个证明项的原始语法字节相同。

## 2. 实际 Family、Comparison、NormalModel 没有被削弱

以去注释/空白后的完整源码片段比对：SchemeLaw、Family、Family.zero、仿射 Comparison、NormalModel、概形 Comparison 均与项目原始声明一致，详见 checks.json 四项片段检查。

Family 的 curve、p、全体概形值点的自然交换群律、proper、相对维数1的smooth、geometrically connected字段完整保留。曲线和结构映射不是抽象占位对象。

两类 Comparison 都保留实际曲线映射、真实 Cartesian square、真实恒等截面方程。没有加入预期判别式相等、任意标架或标量修正字段。

NormalModel 完整保留正规Noetherian整环来源、椭圆方程、总曲线及generic curve整性/局部Noetherian条件、实际群律与原点条件、ℚ代数映射和实际几何comparison。这些条件约束 source model ring；目标 R 仍然仅要求 CommRing/Algebra ℚ R，没有把 R 限制为整环或约化环。

## 3. 任意测试、非约化/非平坦与空概形

Challenge:956 的 SchemeSpecification 量化每个 Type u 上的 CommRing R、每个 Algebra k R、每个椭圆 W、原始Law及IsOriginLaw、每个实际 b:Spec R→S 以及每个 Comparison。该量化与原始 IsD2 逐项相同。正规模型是每个任意测试 R 的来源模型，不是把测试集合改为正规域。

S、T、b、测试R、NormalModel.scalar 均没有 IsReduced、IsDomain、Flat、Noetherian、有限型、准紧或非空的额外约束。因此保留含幂零元的系数环、非平坦底变换以及空概形；b只要求给定的基底结构方程和Comparison的Cartesian/pointed性质。Family本身的smooth/proper是原始研究对象的定义，不是额外限制底变换b为flat。

对于空概形，部分局部量化可以逻辑上为空，但这属于原始范围允许的合法边界，不是将一般对象变成空测试集合。没有仅在几何点或generic fibre检验全局截面相等。

## 4. 非空性和精确5/24归一化

FiveNormalized 保留实际 IsRelativeKato(...,5,g) 与每个实际 GenericComparison 上的 IsKatoFunction(...,5,...)；FiveSpecification 明确 ∃g，随后同时要求该归一化、实际Hodge^24的每个子开集frame条件，以及局部首项条件。它不是“对所有满足某空性质的g”的纯蕴含。

FiveInitial 的式子是函数域内字面的 `5 * g = germ(ε * a^24)`，ε是在整个指定仿射图上的单位；另一个式子在实际Hodge^24层上要求限制后的d等于原点拉回ε乘实际局部相对微分的24次张量。实际恒等理想、5倍映射的torsion理想、IsRegular和理想生成条件均保留。不是仅记录阶数24、首项非零或允许任意标量倍数。

Solution 的 fiveSpecification_iff_localD 用 normalized_unique 将一个存在的g推广到原始localD定义中所需的所有规范化g；反向用 normalized_exists、localD_frame、localD_represents。这确实双向识别原始精确截面。

normal_test_exists 是列入Comparator的独立目标：每个任意ℚ代数上的椭圆W都存在实际NormalModel，并在该模型上存在唯一满足FiveSpecification的d₀。Solution由原始normal_discriminant_model和initialTensorExistsUnique构造它。因此 AffineSpecification 中“所有M、所有d₀满足规格则...”不是依赖未经证明的非空性。

初项公式的局部坐标触发条件本身仍是条件式，这与原始 RepresentsInitial 一致。此次审查没有把它宣称为一个独立的新坐标存在定理；其对localD的唯一刻画由已编译双向桥和原始存在/唯一性提供者支撑。

## 5. 三类 canonical comparison 均被具体公式固定

(1) schemePower：恒等理想核的inclusion兼容条件明确约束实际理想比较，再沿pointed square得到余切比较。canonicalSchemePower要求唯一的24次张量比较，在每个开集每个局部截面的纯张量上满足实际映射公式。Solution先由原始cartesian identity ideal唯一性固定line iso，再由可逆层的局部frame固定tensor iso；compatible_iff_original 和 schemePower_eq_original 识别原始powerIso。

(2) wPower：normalized conormal derivative在所有理想局部截面上规定微分，再用真实family.zero=origin运输；WPowerCompatible在所有局部截面的24次张量上规定power map。wPower_iff_original 和 wPower_eq_original 固定原始weierstrassHodgeIso的24次张量。没有任意Hodge trivialization或单位倍数自由度。

(3) affinePower：AffineLineCompatible 对所有曲线开集、局部函数、共同目标子开集规定pointed relative differential公式。387的kaehler_hom_ext和两次pullback adjunction证明该公式唯一确定原始pointedDifferentialIso；affineLine_iff_original识别原始comparisonHodge，affinePower_iff_original识别原始comparisonPower，affinePull_eq_original识别完整pull。

各 chosen iso 都通过已证明的唯一存在定理选取；选择不是自由替换。Challenge中这些唯一存在是待证明目标，因此必须和最终端点一起提交；当前Comparator确实包含它们。

## 6. Comparator与已存在验证记录

comparator.json 与 Targets.json 均列出10个目标，与Challenge中10个sorry位置一一对应：initialTensorExistsUnique、normalizedConormalHodge、projectiveGeometry、canonicalWeierstrassHodge、canonicalSchemePower、canonicalWPower、canonicalAffinePower、normal_test_exists、scheme_exists、scheme_naturality。没有漏掉支持目标或重复名称。配置只允许propext、Classical.choice、Quot.sound。

反向恢复和iff辅助定理不是Challenge缺口，无需冒充Challenge目标；它们在Solution中提供审查证据。官方Comparator需要对列出的10项全部执行，不能只检查最后两个端点。此处确认的是目标列表完整和源码对应，不是声称官方已经接受配置或递归定义比较已通过。

在报告冻结前已读取到、并核对源码哈希相符的已有结果：Challenge01 exit0/9.78s，Solution01 exit0/187.9s，Audit01 exit0/2.72s，OriginalEndpointAudit01 exit0/2.62s。Solution审计为115个非internal声明、bad=0，每项递归axiom closure均只有标准公理；不能把115描述为审计了所有内部生成声明，但最终目标依赖中若含sorry/非标准公理也会在closure中暴露。ChallengeAudit的23个选定定义检查均只有标准公理，并记录project_imports=[]。385最终receipt也已读入并绑定；本review没有重新执行这些检查。

## 7. 结论的边界与哈希有效性

本包保留并恢复 accepted-080/081 完整输出，未发现需要退回实现的scope缺陷。原始提供者由Solution导入使用，不能将该包描述为完全不依赖原项目证明的新独立证明。Mathlib-only的是Challenge的定义/目标环境。

accepted-080本身明确把完整精确Tate展开协调留给后续consumer；该包不因此自动完成accepted-082或整篇论文，也没有单凭此scope review建立所有独立判别式多项式/乘积等式。源命题与最终数学论文措辞之间的全篇核对不在此次范围。

inputs.json列出本次读取的精确输入哈希；receipt.json只对这些未变内容有效。如果385后续改动Challenge、Solution、Comparator或原始定义，必须更新相应核对。编译和原始端点类型审计已通过，不等于Palomar官方语义或独立内核检查通过。
