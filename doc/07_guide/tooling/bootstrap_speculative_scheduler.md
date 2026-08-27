# Bootstrap Speculative Scheduler

`scripts/bootstrap/bootstrap-strategy.sh` is the compatibility supervisor above
the existing `bootstrap-from-scratch.sh` trust engine. The engine still owns all
compiler production, smoke admission, provenance, Stage 3 verification, Stage 4
admission, deployment, and rollback evidence. The supervisor does not mint a
compiler or substitute a planner receipt.

## Normal use

Keep using the canonical entrypoint:

```sh
scripts/bootstrap/bootstrap-from-scratch.sh \
  --strategy=full \
  --bootstrap-receipt=build/bootstrap/planner-admission.env \
  --full-bootstrap --deploy
```

The entrypoint delegates coordinated `normal` and `full` runs to the supervisor.
`adhoc`, receipt validation, single-stage stop/resume, diagnostics, SimpleOS,
and FreeBSD recovery lanes remain direct stage-engine operations.

The supervisor deliberately leaves the engine's missing/malformed planner
receipt preflight untouched. No receipt means no scheduler generation and no
compiler execution.

## Scheduling contract

The immutable graph authority is
`scripts/bootstrap/bootstrap-graph.sdn`. A run creates
`OUTPUT/scheduler/bootstrap-<time>-<pid>/` containing:

| Record | Meaning |
|---|---|
| `graph.env` | exact graph, source/policy generation, resource reservations, and quarantine root |
| `generation.lease.env` | current, tainted, or qualified lease; task publication binds its hash |
| `events.env` | machine-readable task/generation transitions |
| `tasks/*.env` | typed exit/status receipts bound to the original current lease |
| `qualification.result.env` | independently reverified Stage-2 admission plus the broad hello-world native-build gate |
| `stage3.result.env` | reverified Stage-3 provenance/candidate bound to the qualified parent admission |
| `lineage-admission.env` | immutable qualified ancestor-chain admission, written before any Stage-4 continuation |
| `stage4.result.env` | reverified continuation, Stage-4 artifact/provenance, lineage, and publication result |
| `failure-manifest.env` | failure root, task completeness, source/policy/graph/lease identities, and invalidation disposition |
| `invalidations/*.env` | recursive Stage 2 → Stage 3 → Stage 4 → deploy → release revocation receipts |

After Stage 2 publishes its immutable smoke-admission receipt, the stage engine
immediately starts Stage 3 on the compiler critical path. With at least two CPU
slots and enforceable per-child memory limits, the supervisor concurrently rechecks
the admission and runs `check-stage2-hello-world-native-build.shs`. This is a
real compiler qualification: it builds/executes the `--entry` form and checks
the positional form for crash/hang. It is not a sleep-only planner.

`SIMPLE_BOOTSTRAP_SCHEDULER_CPU_SLOTS` and
`SIMPLE_BOOTSTRAP_SCHEDULER_MEMORY_MIB` may cap the scheduler. The supervisor
passes bounded thread counts to both compiler children and enforces each memory
claim with the shell's `ulimit -v`. One CPU slot, insufficient memory (including
the safety reserve), or a platform without `ulimit -v` selects
`serialized-resource-guard`: Stage 3 completes before broad qualification, so
unenforceable claims never overlap. `graph.env` records the actual enforcement
mode and limits. Deploy remains an exclusive token.

## Quarantine and continuation

Stage 3 is speculative while its Stage-2 parent is only smoke-admitted. The
supervisor strips `--full-cli`, `--deploy`, and `--release` from that provisional
engine invocation. The supervisor re-verifies the real qualification gate log,
Stage-2 admission/candidate, and Stage-3 provenance/candidate under the same
current lease, then writes and re-verifies `lineage-admission.env`. Only that
hashed receipt authorizes the shipped entrypoint to start Stage 4. Environment
booleans and alternate engine/qualifier paths are not authority.

- `--full-cli` uses the admitted Stage-3 continuation and records
  `publication_status=quarantined` without touching `bin/release`.
- `--deploy` and `--release` build and verify Stage 4 in quarantine, then return
  fail-closed with `promotion-required.env`. The current engine cannot yet
  separate its deploy/release mutation from its long Stage-4 build, so the
  supervisor will not pretend that an early admission remains current. A future
  explicit post-admitted promotion command must consume that receipt.

After the Stage-4 child exits, the supervisor rechecks the exact generation
lease, source/input digest, policy hash, lineage, qualification result, Stage-2
admission, Stage-3 provenance, and Stage-4 result. It repeats the immutable
barrier immediately before qualifying the lease. Drift writes recursive
invalidation evidence and never rewrites a stale lease as qualified. A still
current lease is atomically replaced with a tainted receipt; an externally
tainted/stale lease is preserved. The qualified lineage is moved to revoked
evidence and replaced by an invalidated receipt, while `failure-manifest.env`
and `current.env` both report failure, leaving no reusable qualified state.

No provisional child may update `bin/simple`, protected checks, release state,
or trusted shared publication records.

## Failure and recovery

A correctness/qualification failure, engine failure, source or policy drift,
unknown failure, or stale lease taints the generation. The supervisor cancels
the live descendant for `normal`; `full` lets selected tasks reach terminal
inventory. In both cases it writes recursive invalidation receipts and preserves
the artifacts as tainted evidence. It never deletes them or silently reuses them.

Repair the failure, obtain a planner receipt bound to the repaired inputs, and
start a new generation. Do not edit a failed generation's lease or receipts.
The existing `--resume-stage3-from-admitted` and
`--resume-stage4-from-admitted` commands remain the recovery stage boundaries;
their provenance checks still apply.

## Compatibility boundary and migration

The shell supervisor is the complete smallest viable scheduler for the current
monolithic engine. It intentionally refuses coordinated `--clean-release` and
`--mode=one-binary` rather than weakening their cache/deployment semantics; use
`--strategy=adhoc` for those legacy lanes until isolated continuations exist.

The planned pure-Simple scheduler must consume the same graph/lease/task/failure
contracts, then replace polling with typed engine events and extracted
idempotent `bootstrap step` tasks. The recovery shell remains. Migration must not
relax planner admission, immutable parent/source/runtime/tool bindings, private
caches, sanity/receiver/native-build gates, Stage-3 provenance, Stage-4 checks,
or exclusive deployment.

## Focused verification

```sh
sh test/01_unit/scripts/bootstrap_scheduler_contract_test.shs
sh test/01_unit/scripts/bootstrap_strategy_fallback_contract_test.shs
sh -n scripts/bootstrap/bootstrap-strategy.sh \
  scripts/bootstrap/bootstrap-qualify-stage2.shs \
  scripts/bootstrap/bootstrap-scheduler-contract.shs
```

The scheduler test invokes the side-effect-light contract helpers directly. It
uses adversarial receipts for path escape, hash drift, tainted lineage, mutated
Stage-4 output, recursive invalidation, and verifies that production engine or
qualifier override variables are inert. No test-only bypass exists in the
shipped supervisor.
