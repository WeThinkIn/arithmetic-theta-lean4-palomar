# Official split-square-degree preflight: Solution-build memory exhaustion

Official run [39552048056](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39552048056), bound to commit `2c85e9b977f3d8e91570235a68534c945d69ff28`, ended with `infrastructure/resource-exhausted`. The authoritative mechanical report identifies `solution-build` as the last active stage: exit 137, systemd `oom-kill`, seven OOM-kill events, and a cgroup memory peak of 15,828,697,088 bytes. No supervisor deadline fired.

The report does not establish a successful Solution build, comparator pass or independent-kernel acceptance for this official run. The preliminary comparator-configuration checks and the configured kernel list must not be confused with completed mathematical comparison or kernel replay.

The frozen split-square-degree export already passed the local stock comparator and all three kernels, as documented in [split-stock-kernels-574](../split-stock-kernels-574/). This is separate evidence: the official runner must first build the project from its fresh build directory under its resource limits. The earlier split-discriminant run 39552053781 failed in the same Solution-build stage; the older compact-unary run 39541709031 instead completed its build and exhausted memory in the comparator stage.

No unchanged retry has been dispatched. The ongoing local cold-build profile 582 investigates the shared split-discriminant dependency closure with four CPUs, compiler-j1 and a 14 GiB cgroup cap. Its shared external dependency cache and cgroup-v1 accounting differ from the official runner; it is not proof that either official package fits. Full accepted-074 scope is preserved. Whole-paper review, intake and registration remain incomplete.
