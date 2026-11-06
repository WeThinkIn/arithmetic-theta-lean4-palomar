# Official split-discriminant preflight: Solution build memory exhaustion

Official run [39552053781](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39552053781), bound to commit `2c85e9b977f3d8e91570235a68534c945d69ff28`, completed with an infrastructure/resource-exhausted error. The authoritative report identifies `solution-build` as the last active stage and records `exit 137`, systemd `oom-kill`, and seven OOM-kill events. The observed host has four effective CPUs and 16,766,414,848 bytes of RAM; the recorded build cgroup memory peak is 15,900,200,960 bytes. The report does not identify the individual compiler or module responsible.

This run did not produce an official independent kernel verdict. The complete local stock three-kernel passes recorded in `../split-stock-kernels-574/` concern separately checked frozen exports; they do not supersede this official build failure. The original accepted-073 theorem scope is retained.

An unchanged official retry has not been dispatched. A new isolated cold-build diagnostic of this exact source commit records concurrent compiler use and memory, using only pinned external dependency caches. Its local cgroup v1/shared-cache accounting differs from the official runner, so it is diagnostic evidence, not official capacity equivalence. Whole-paper verification and registration remain incomplete.
