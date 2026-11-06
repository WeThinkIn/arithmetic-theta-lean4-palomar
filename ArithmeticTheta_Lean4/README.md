# Arithmetic Theta Series — Complete Lean 4 Formalization

本目录收录论文的完整原始 **Lean 4 形式化证明**，包含源码、数学阅读导引、固定依赖、
复现工具和验证报告。数学家审阅证明可从[阅读导引](READING_GUIDE.md)开始，再通过
[定理索引](THEOREM_INDEX.md)定位具体声明。

This directory contains the complete original Lean 4 formalization accompanying
the paper on the purely arithmetic characterization of linear relations among
theta series of quadratic lattices. The development determines the full relation
kernel, constructs an image basis and rational reconstruction coordinates, and
provides the arithmetic and geometric constructions supporting these conclusions.

The pinned toolchain is **Lean 4.33.1**. The readability edition contains
**1,199 proof modules** and preserves **103 original theorem endpoints**. Its
recorded full build, exact-type checks, transitive-axiom checks and declaration
preservation results are described in the [verification notes](verification/README.md).

## Start here

| Purpose | Entry point |
| --- | --- |
| Understand the mathematics and proof structure | [Reading guide](READING_GUIDE.md) |
| Find each of the 103 original theorem endpoints | [Theorem index](THEOREM_INDEX.md) |
| Read the main kernel, image and reconstruction theorem | [ConservativeImageConsumerR0268.lean](Lean/ConservativeImageConsumerR0268.lean) |
| Inspect the joint proof entry point | [GoalRoot.lean](Lean/GoalRoot.lean) |
| Install the pinned dependencies and reproduce the checks | [Reproduction instructions](REPRODUCE.md) |
| Review the recorded verification evidence | [Verification notes and reports](verification/README.md) |
| Read the accompanying paper and formalization mapping | [Publication materials](publication/) |

The [Palomar adaptation](../Palomar_lean/README.md) is maintained separately with
Lean 4.35.0-rc2 and its own independent verification interfaces. Use the
instructions in this directory for the original Lean 4.33.1 development.

This directory was previously named `local-reproduction/`. That rename changed
navigation and documentation and preserved the then-current Lean sources,
dependency pins, original contract, verification probes and reproduction scripts.
Historical reports retain their recorded paths and hashes. See the
[directory-rename record](verification/DirectoryRenameReport.json) for the
static preservation checks performed for that change. Subsequent source
readability changes are documented in the [reading guide](READING_GUIDE.md)
and [verification notes](verification/README.md).
