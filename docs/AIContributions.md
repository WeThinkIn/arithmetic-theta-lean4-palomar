# AI contribution disclosure

Human author and responsible maintainer: **Jue Ding**.

Codex contributed to the mathematical construction and proof development underlying
this project, as well as to its Lean formalization. The original mathematical task
explicitly records “Exploratory Proof Agent: Codex mathematical construction” in
its author field. This contribution therefore includes mathematical construction,
in addition to software translation and proof implementation.

The WujieAI Lean4 Agent and Codex were used in the Lean proof-development workflow,
including implementation, debugging and integration. Codex also assisted the
independent adaptation from Lean 4.33.1 to Lean 4.35.0-rc2, preparation of scoped
Challenge/Solution interfaces, and build, comparison and verification tooling.

The source for the mathematical-construction attribution is
[`paper/OriginalTask.tex` at commit 4085af9d0f57a23c83e73eba9b550733a8db1c68](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/blob/4085af9d0f57a23c83e73eba9b550733a8db1c68/paper/OriginalTask.tex#L16).
The source paper is retained as provenance; the accompanying revised manuscript
records its own author and contributor information.

AI systems are disclosed in the `automation` metadata. The human-only
`project.authors` and `project.responsible_maintainers` fields remain Jue Ding.
Third-party mathematical libraries retain their own attribution and licenses.
This account does not assign a quantitative share of individual results to a
particular model or equate AI-assisted development with independent verification.
Verification claims remain tied to their recorded source revisions and scopes.
