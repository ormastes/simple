# Stage-bound bootstrap test tasks

The canonical `bootstrap-managed-phases.shs` accepts a pinned N-task graph through
`--task-inventory`, `--task-inventory-sha256`, `--task-policy`, and
`--task-policy-sha256`. This routes to the compiled `buildrunner managed-tasks`
owner. The existing two-driver invocation remains compatible. It builds its
Phase4 products with the admitted Phase2 producer: this is early Phase4 evidence,
not proof of a proper Phase3-to-Phase4 chain.

Each admitted test-product task invokes `run-stage-task-test.shs` with pinned
compiled `aggregate_task_main` and `aggregate_task_verify_main` executables,
identity and product manifest paths/hashes, private report/database roots, and
`--threads=80`. Its explicit stage is one of `P2`, `earlyP4-fromP2`, or
`properP4-fromP3`. The last stage requires manifests bound to the actual
Hello-qualified Phase3 producer. Caller-bound manifests confer no admission.

The adapter keeps execution and verification in the same working directory and
environment. Verification reads the retained enumeration and the PureDB snapshot;
it never executes another test callback. Complete test failure returns 1. Missing,
changed, incomplete, contradictory, or crash-masked evidence returns 2. The
BuildRunner parent must reap the entire task tree before dependent scheduling.
Each independent compiler/interpreter/loader product for each backend remains a
separate DAG task; an unavailable product must have an explicit blocked outcome,
not an omitted inventory row. Global resource admission remains with that parent.

The graph builder must publish a new immutable epoch after actual Phase3 output
and Hello qualification, retaining the previous snapshot/receipt links. Automatic
epoch expansion and default complete graph generation are still unfinished;
this hook accepts an already prepared admitted graph and does not fabricate one.

Validation: seven shell transport contracts passed (success, ordinary failure,
invalid summary, crash-like exit with stale success, contradictory exits, and
successful continuation). These are not native suite results. The compiled
verifier and complete bootstrap graph require native validation before a full
qualification claim.
