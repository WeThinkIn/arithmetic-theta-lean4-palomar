# Local Lean 4.33.1 rebuild verification

`LocalRebuildReport.json` records a new full rebuild using this directory's scripts: all 1,199 proof modules freshly compiled, followed by 103 exact-type/axiom checks. External libraries are the fixed precompiled release assets. `LocalRebuildSummary.json` binds this report to the input manifest and records packaging checks. These generated reports are outputs, not inputs listed in SHA256SUMS.

本次报告对应仓库 local-reproduction 中的独立复现脚本。全部 1,199 个论文模块重新编译，103 项检查通过；它不替代 publication 中的原项目合同审计，也不声称从零重建外部库。
