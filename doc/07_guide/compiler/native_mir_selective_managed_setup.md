# Migrate explicit selective MIR to managed Linux workers

Status: source candidate. Runtime/compiler/spec execution, actual managed tree
lifecycle and job10/performance qualification remain UNRUN. This guide does not
admit a cached tool or authorize a build under an occupied resource allocation.

`SIMPLE_MIR_SELECTIVE=1` now requires the managed Linux broker. Missing broker
configuration, unsupported platform/delegation, mismatched image pins, missing
broker memory estimate or an unbounded worker lifetime fails before the retained
HIR exporter or any MIR worker starts. Explicit selective mode never silently
switches to serial/integrated compilation or raw PID management.
`SIMPLE_MIR_SELECTIVE=0` does not invoke this preflight and gains no broker setup
requirement; the existing nonselective route remains separately qualified.

## Cached tool provenance

Supply an already qualified cached executable for
`src/app/bootstrap_builder/native_group_linux_broker.spl`. It must implement
version-three `native-worker-v1` requests, broker-issued actual child PID/birth
receipts, and the matching existing Linux pidfd/cgroup runtime owner including
its retained-child metadata ABI. A group-root-only older broker is insufficient.
The compiler child must be this exact running cached CLI image; its existing
compiled internal worker route is used, not a new source runner.

The repository currently has no authenticated generic broker-discovery registry
that this CLI can consume. The parser inspection registry is domain-specific
and blocked; SimpleOS tool inventories do not issue this host broker authority.
Therefore setup is explicit. Obtain the expected executable path and SHA256
from the existing qualification/release owner, retain its producer/source,
runtime and real lifecycle evidence, then supply those exact values below.
Computing a digest of an arbitrary local executable is a content pin, not
admission. This CLI neither creates an approval receipt nor promotes a pin into
qualification. Diagnostic/provisional image receipts are not qualified tools.

The existing image-producing route is
`scripts/bootstrap/prepare-phase2-build-manager.shs`, using an admitted Stage 2
producer receipt, matching frozen source/runtime, explicit target, runtime bundle,
output root and resource cap/reserve. It builds the existing `group-broker`
entry and seals `manager-images.env` with `group_broker` and
`group_broker_sha256`, alongside producer/source/runtime lineage. This is an
image/lineage preparer, not a substitute for actual V3 broker and lifecycle
qualification. Do not invoke it from the native-build hot path, reuse an old
runtime without the new ABI, or mutate a frozen campaign to manufacture a tool.
The provisional preparer explicitly emits `diagnostic_only=1` and is not an
admission source. Until the qualification owner provides a suitable cached
image, explicit selective mode is unsupported rather than falsely approved.

## Host and resource requirements

The existing Linux owner needs cgroup v2 with a writable owned/delegated parent,
`memory` delegated to children, usable `memory.max`, `memory.peak`,
`cgroup.events` and `cgroup.kill`, plus pidfd/clone3/execveat support. Provision
that boundary through the host's existing resource/delegation owner. The CLI
does not enable controllers or change permissions on an unowned host subtree.
Its existing capacity probe checks prerequisites and may create/remove one empty
private capability cgroup; it launches no compiler child. A denied or missing
controller returns an explicit unsupported/admission diagnostic before export.
This snapshot is not a reservation or a guarantee of later spawn success.

Retain measured estimates for the parent, one worker and its tools, one broker,
and exporter. `WORKER_KIB` limits the worker/tool cgroup; `BROKER_KIB` is added
per admitted slot in the enclosing phase/tree calculation. Include broker image
pinning, request/receipt metadata and private log/object space in the estimates
and disk reserve. Keep the existing enclosing process-tree/cgroup budget and
watchdog; do not add competing heavy work based only on these environment values.

## Explicit invocation

The variables named `qualified_*`, `measured_*`, `allocated_*` and `reserved_*`
below are inputs from the real qualification/resource owners, not values to
invent from filenames or a fresh self-hash. Select a finite worker timeout of
1..86400 seconds. Do not use `--timeout 0` with explicit selective mode.

```sh
SIMPLE_MIR_SELECTIVE=1 \
SIMPLE_MIR_GROUP_BROKER_PROGRAM="$qualified_cached_broker" \
SIMPLE_MIR_GROUP_BROKER_DIGEST="$qualified_broker_sha256" \
SIMPLE_MIR_SELECTIVE_PARENT_KIB="$measured_parent_kib" \
SIMPLE_MIR_SELECTIVE_WORKER_KIB="$measured_worker_and_tools_kib" \
SIMPLE_MIR_SELECTIVE_BROKER_KIB="$measured_broker_kib" \
SIMPLE_MIR_SELECTIVE_EXPORTER_KIB="$measured_exporter_kib" \
SIMPLE_MIR_SELECTIVE_PHASE_KIB="$allocated_phase_kib" \
SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB="$allocated_tree_kib" \
SIMPLE_MIR_SELECTIVE_DISK_BYTES="$allocated_disk_bytes" \
SIMPLE_MIR_SELECTIVE_DISK_RESERVE_BYTES="$reserved_disk_bytes" \
"$qualified_cli" native-build --source src --entry "$explicit_entry" \
  --entry-closure --backend cranelift --target "$qualified_target" \
  --runtime-path "$qualified_runtime" --jobs 10 \
  --timeout "$worker_timeout_seconds" --output "$owned_output"
```

Actual admitted worker count is constrained by the resource owner. This command
alone is not evidence of ten overlapping physical codegen jobs or quiescent
cancellation. Unsupported bootstrap/context routes remain guarded.

## Existing acceptance fixture

`test/03_system/native/native_mir_selective_process_spec.spl` now requires the
broker program, external expected digest and broker RSS estimate in addition to
its existing qualified runner/compiler/runtime and phase/tree/disk inputs. It
uses the same broker preflight before its matrix. The fixture explicitly passes
managed configuration only to selective runs and clears inherited private owner
state. Nonselective comparison runs have broker inputs removed.

Set `SIMPLE_MIR_SELECTIVE_TEST_WORKER_TIMEOUT_MS` to a measured finite
1000..86400000 ms, and set `SIMPLE_MIR_SELECTIVE_TEST_TIMEOUT_MS` larger than the
worker lifetime plus 30000 ms cleanup and the remaining measured pipeline time.
The fixture passes the worker timeout explicitly to native-build. Its missing
broker scenario intentionally omits configuration, requires the real early
rejection, and observes no MIR invocation/export directory or final program.
No success stub, source-text assertion or silent skip supplies this evidence.

Pure prerequisite-reason unit cases do not probe the kernel. All actual tests,
including this migration scenario, remain UNRUN until the qualified runner,
cached broker, host delegation and a fresh resource allocation are available.
