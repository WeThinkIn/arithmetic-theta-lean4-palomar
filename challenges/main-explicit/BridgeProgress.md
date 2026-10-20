# 主 Challenge 定义桥进展

初始 SemanticMapping.md 保留检查时的原始内容和哈希。

上述表格记录初始规格检查时的桥接计划。后续 attempt 198 已核检查其中一部分，具体边界如下；完整 Solution 仍未完成。

### 定义桥的实际检查进展（attempt 198）

`bridges/ReadyBridges198.lean` 导入实际已编译的原实现模块，20 个引理均通过。已检查 validGram、theta、thetaMap、确定性整数正交化、真实预像商及代表谓词、levelIndex 的定义桥，以及实际壳层有限性和壳层矩阵复延标量一致性。矩阵桥消费原 `computed_coefficient_matrix`，没有把可执行枚举与壳层计数直接视为定义相等。

`bridges/IndexingBridges198.lean` 已检查 commonN/centered、新旧 Indexing 双向字段转换、count 保留、Indexed 等价和往返恒等式。不过它当前导入从原文件逐字提取的纯算术定义前缀；完整 `LatticeGlobalSectionsDefinitionsR0188` 尚未编译就绪。必须在真实模块可用后替换前缀导入并重验，才能用于最终 Solution；不可同时导入两个同名声明来源。

检查无 sorry/admit 或新增公理声明，已打印的公理闭包只有 propext、Classical.choice、Quot.sound。原始规格、源切片和依赖哈希、命令及终态见 `bridges/receipt.json`。这些结果尚不包含完整 cutoff 桥、accepted-037 主定理组装或 Comparator 通过。

