# Sharp arithmetic theta bound, adaptive solver and exact image

**Official full mechanical preflight passed** at commit `561a253f79bc11127fb0a4bc72865f23470e0ca6`. Stock Lean, NanoDa and Conron accepted the Solution. The Challenge received high-trust provenance. See the [official report and exact scope](../../docs/audit/official-sharp-adaptive-image-2079/Review.md).

This package covers seven complete original endpoints: accepted-046, accepted-049, accepted-064 through accepted-067, and accepted-088. It preserves the distinct-norm sharp cutoff, full theta-kernel determination for every larger prefix, the executable first-certified-stop solver, checked integral changes, and full nullspace/image/unique-coordinate output. Rank zero, singleton cutoff zero, empty or invalid candidate changes, and the original source hypotheses remain explicit. Finite-shell support accompanies the actual cardinality-defined complete theta series.

The verified Challenge is 31,350 bytes and 488 lines. It imports Mathlib and the canonical Lean core module `Lean.Meta.Match.Match`. The Solution uses the real implementation and does not import the Challenge. The seven configured targets include a combined sharp result recovering two original endpoints and the auxiliary `shellFinite` obligation. The frozen [Scope.json](Scope.json) and initial receipts retain their original preparation-time fields; the later official report records completed mechanical verification.

The seven endpoints add to a historical union of 89/103 original endpoints with official mechanical evidence at their respective revisions. The full original scope remains 13 requirements and 103 endpoints. Whole-paper semantic acceptance and registration remain incomplete.
