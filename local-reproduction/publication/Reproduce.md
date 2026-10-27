# Reproduce the editorial successor

This revision changes exposition, related-work positioning and verification documentation. All 1,199 Lean files and all 103 exact obligation records are identical to the accepted arithmetic-theta-full-source-v3-r0268 delivery. The original accepted delivery is retained unchanged. The new delivery contract changes the output location and adds provenance bindings; it does not change any theorem type or mathematical hypothesis.

## Environment

Project root: `/home/wujie-ai-lean4-proof-agent-program`. Lean **4.33.1**, pinned by `lean-toolchain`. Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`; auxiliary pins are in the project's `lake-manifest.json`. Use the prewarmed project library environment and preserve `LEAN4_AUDIT_CACHE_ROOT` when configured. By default the authority auditor uses `workspace/lean-audit-cache`. Python: `/home/miniconda3/envs/lean4/bin/python`.

## Contract and preserved evidence

Successor contract: `workspace/goal-tasks/arithmetic-theta-editorial-20261022/contract.json`. SHA-256: `63f94d525f2e2d08ce496c2adffc7e5d950aa1dfe5b4dcbaf3478be7a8d3fb59`. The original mathematical objective and 103 obligation records are unchanged. Additional inputs bind the original contract, source closure, manuscript, original delivery manifest and editorial objective. `FormalizationMapping.md` retains the original mathematical mapping; its historical inventory describes the original integration task. `RevisionNotes.md` records this editorial revision's scope. This source delivery alone is not a standalone copy of every external library and contract input.

## Structure, PDF preflight and audit

Run from the project root. Compile the paper in a separate build directory before the full audit. Three pdflatex passes resolve references. Use the authority CPU-affinity wrapper for the complete audit; it validates or rebuilds modules using the shared verified cache, then checks exact types, axioms and current source/input bindings and compiles the paper.

```bash
cd /home/wujie-ai-lean4-proof-agent-program
/home/miniconda3/envs/lean4/bin/python tools/check_goal_paper.py --project-root . --contract workspace/goal-tasks/arithmetic-theta-editorial-20261022/contract.json
/home/miniconda3/envs/lean4/bin/python tools/codex_goal_affinity_exec.py -- /home/miniconda3/envs/lean4/bin/python tools/audit_goal_delivery.py --project-root . --contract workspace/goal-tasks/arithmetic-theta-editorial-20261022/contract.json --timeout 1200 --summary
```

The generated `AuditReport.json`, `ProofStatus.json` and `DeliveryManifest.json` bind this revised paper and the unchanged Lean source closure. Read them only after the audit reaches its terminal result. No copied historical success report serves as this revision's acceptance.

## Verification scope

The audit verifies formal propositions, types, dependencies and axiom closures. Mathematical correspondence to the prose requires review; historical priority is not a result of compilation. The arithmetic modular-form scope, supplied representative-completeness hypothesis and absence of a general tractability claim are unchanged. The source companion Python programs are provenance and are not required executables of this Lean delivery.
