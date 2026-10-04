# Aggregate test TaskRunner entry

Implementation status: source integration candidate; native and interpreted
execution proof is **UNRUN**. This does not qualify a bootstrap stage.

Compile `src/app/test/aggregate_task_main.spl` with the admitted stage producer.
The bootstrap DAG invokes that compiled entry once for each independent product,
collects its summary even on nonzero exit, and continues all other products.
Do not execute this source using a Rust seed as a tooling fallback.

The entry accepts only `--name=value` options:

- `stage`: `P2`, `earlyP4-fromP2`, or `properP4-fromP3`.
- `backend`: `llvm` or `cranelift`.
- `identity-manifest`, `identity-manifest-sha256`: frozen identity input.
- `inventory-manifest`, `inventory-manifest-sha256`: frozen product input.
- `report-root`: existing fresh private directory for enumeration, attempt
  ledgers, and `summary.env`.
- `db-root`: private session/cache database root owned by one parent writer.
- `threads=80`: orchestration worker policy. This individual product parent
  executes its groups sequentially; it does not claim 80 concurrent test children.

All path options are absolute. The entry refuses an existing summary and each
attempt refuses an existing ledger. It never overwrites earlier evidence.

The identity manifest has one `key=value` per line and a final newline:

```text
format=SIMPLE-AGGREGATE-TASK-IDENTITY-1
stage=P2
backend=llvm
run_nonce=<unique parent-owned run identifier>
producer_path=<actual stage compiler binary>
producer_digest=<SHA256>
source_path=<canonical source snapshot receipt>
source_digest=<SHA256>
runtime_path=<canonical runtime receipt>
runtime_digest=<SHA256>
toolchain_path=<canonical toolchain receipt>
toolchain_digest=<SHA256>
policy_path=<frozen task/resource policy>
policy_digest=<SHA256>
execution_path=<frozen logical invocation and fixture/config manifest>
execution_digest=<SHA256>
```

Every referenced file is hashed before enumeration. Digest binding is distinct
from semantic admission: the existing bootstrap verifier must validate the
receipts and actual stage lineage. No manual manifest creates source authority.
The entry always reports `provenance_status=caller-bound-unadmitted`.

The shared owner `std.test_runner.aggregate_task_manifest` provides
`aggregate_task_manifest_read_v1(identity_path, identity_sha, product_path,
product_sha, stage, backend, report_root)`. It hashes the actual bounded text
payload it decodes and returns `AggregateTaskManifestV1` with the frozen
identity template and command. The compiled entry and DAG use this same decoder.
After successful binary enumeration,
`aggregate_task_manifest_identities_v1(bound, inventory)` constructs the exact
registered identities before execution. The inventory header must match the
bound product and an empty inventory is rejected.
`aggregate_task_manifest_summary_expected_v1(bound, inventory, db_root)` creates
the typed expectations for independent summary/snapshot verification, including
the same group nonce. These APIs validate caller bindings; bootstrap admission
still belongs to the canonical receipt owner. Their native execution remains
unverified until the shared runner closure is compiled and tested.

The product manifest describes the existing generated registry entry:

```text
format=SIMPLE-AGGREGATE-TASK-PRODUCT-1
subsystem=compiler
runtime_mode=native
program_path=<compiled aggregate product>
program_digest=<SHA256>
artifact_path=<same compiled aggregate product>
artifact_digest=<SHA256>
whole_inventory_digest=<source-specs.tsv SHA256 from product build receipt>
subset_digest=<subsystem subset SHA256 from product build receipt>
prefix_count=0
```

`subsystem` is compiler, interpreter, or loader. For interpreted execution,
`runtime_mode=interpreter`, `program_path` is the actual interpreter executable,
`artifact_path` is the generated source entry, and `prefix_0` through
`prefix_N` contain its existing supported invocation arguments. The parent
appends the existing `--enumerate` or `--run`, `--registry-output=...`, and exact
case selection arguments. This interface does not claim that an untested
interpreter invocation supports the registry; enumeration must actually succeed.

The entire registry is enumerated before any test/hook callback. The parent
registers that expected inventory in the shared PureDatabase and consults exact
identity crash history before scheduling. Normal cases stay grouped; known
crash cases start isolated. Ordinary assertion failures remain terminal and
later cases continue. Confirmed crashes preserve validated completed member
results; only unresolved members receive fresh isolated processes, at most
three attempts. Timeout, cancellation and infrastructure failure are distinct
from a confirmed crash. Unproven process cleanup blocks further unsafe process
admission; it cannot produce a fake reaped receipt.

`summary.env` uses `format=SIMPLE-AGGREGATE-TASK-SUMMARY-1` and records stage,
backend, runtime mode, subsystem, all input identity hashes, actual program and
artifact hashes, parent environment hash, expected enumeration hash/count,
`pass`, `fail`, `crash`, `skip`, `pending`, `abort`, and `notrun` counts. Those
seven terminal counts sum to expected count. `exhausted` is an overlapping
retry-budget measure and `crash_attempts` counts historical attempts within this
run; do not add either to the inventory count.

The summary also binds `task_db_revision` and `task_db_identity` to the actual
durable WAL snapshot. `completion=1` means collection and durable snapshot
completed, not that tests passed. `aggregate_exit` stays nonzero for any failed,
crashed, exhausted, aborted, pending, or unrun case, a transport failure even
after successful recovery, or zero passing cases. Setup/enumeration failure
writes `completion=0`, `expected_count=-1`, and `aggregate_exit=2`; unavailable
inventory is never reported as zero passing tests. The DAG must hash the
summary as a declared output and must not admit an exit-zero process alone.

Current limitations: the new completion provider is Windows JobObject owned;
POSIX completion is deliberately unproven until connected to its authoritative
process owner. Unknown setup crashes cannot identify a culprit merely from
the last declaration. Source registration/setup can still execute before a
selected case; the complete registry and fixture failures remain explicit.
This entry requires a fresh run nonce/report directory. Persisted history affects
isolation in a newly requested run; automatic resume after a parent crash is not
implemented. The DAG must not restart completed green product tasks as a retry.
