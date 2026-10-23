# Common-unary official worker-time exhaustion

[Official preflight 39962946907](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39962946907), at commit `561a253f79bc11127fb0a4bc72865f23470e0ca6`, ended with `infrastructure/resource-exhausted` and `last_active_stage: comparator`. The provider reports that the worker wall-clock capacity was exhausted.

Solution compilation completed successfully in 14,418.981 seconds, and Solution export completed successfully in 200.735 seconds. The reported Solution-build memory peak was 14,559,051,776 bytes; no OOM kill was recorded in the report. The comparator supervisor timed out. No independent-kernel acceptance result was recorded, so this run adds no official endpoint coverage. The available comparator telemetry does not establish which internal checker consumed the time and is not a theorem counterexample or a kernel rejection.

The [diagnosis](diagnosis.json) verifies report and source bindings. The complete Challenge retains the original accepted-071 scope and all 39 configured obligations. The separately published rendering repair addresses presentation compatibility; it does not establish that the workload fits the worker time budget. A further retry requires a justified resource or runtime improvement, or supported additional capacity. No unchanged retry or capacity request has been made here.
