# Official common-unary preflight: Solution-build memory exhaustion

Official run [39557005985](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39557005985), bound to commit `77c9bffc2e3ce0ab8141cda8b3b4054b054b7265`, ended with `infrastructure/resource-exhausted`. The mechanical report identifies `solution-build` as the last active stage: exit 137, systemd `oom-kill`, seven recorded OOM-kill events, and a cgroup memory peak of 15,876,751,360 bytes. No supervisor deadline fired.

No successful official Solution build, full comparator result or independent-kernel pass follows from this report. The report's configured kernels and preliminary configuration checks are not kernel verdicts. The local common-unary run568 has passed con-ron and NanoDa, while its stock Lean default replay remains pending. Instrumented diagnostic593 is separate and cannot replace stock acceptance.

This is the third recent cold-build memory failure after split-discriminant581 and split-square-degree596. The older compact-unary592 failed later, in the comparator stage after successful Solution compilation. These stages require separate resource diagnoses. No unchanged retry has been dispatched.

The local cold-build profile582 and per-declaration replay593 remain active. A read-only overlap analysis602 observes four simultaneous compiler processes with a combined RSS near the build memory ceiling. This does not establish identical accounting on the official host or identify a mathematical failure. Full original accepted-071 scope and all hypotheses remain unchanged; whole-paper semantic review, intake and registry acceptance are incomplete.
