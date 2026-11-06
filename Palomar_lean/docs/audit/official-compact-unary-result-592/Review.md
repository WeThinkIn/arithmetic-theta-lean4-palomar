# Official compact-unary preflight: comparator memory exhaustion

Official run [39541709031](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39541709031), bound to commit `effce98775aa7da461e6a3b7b7992e8352e95293`, completed with `infrastructure/resource-exhausted`. The authoritative report identifies `comparator` as the last active stage, with `exit 137`, systemd `oom-kill`, seven OOM-kill events and a recorded cgroup memory peak of 16,058,015,744 bytes. No supervisor deadline fired.

The Solution build succeeded: the report records return code 0, an elapsed time of 11,434.859 seconds and a successful 11,794-job build. This distinguishes the result from the separate split-discriminant preflight 581, which exhausted memory during Solution build. The comparator-stage label does not isolate export parsing, structural comparison or a particular kernel replay. The configured kernel list is not a set of passing kernel results. No official comparator or independent-kernel pass is inferred.

This run checks the older effce987source revision. It does not establish the result of either currently running full common-unary run 39557005985 or split-square-degree run 39552048056. An unchanged compact-unary retry has not been dispatched.

A separate local diagnostic profiles declaration-by-declaration replay of the current frozen common-unary export 567, with local RSS/time guards, while preserving the live stock check 568. This is useful for locating shared expensive proofs but is not an exact reproduction of the older official export or its aggregate cgroup. Scope remains the full original accepted-028; whole-paper verification and registration remain incomplete.
