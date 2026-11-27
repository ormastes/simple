# Owned piped process V2 acceptance manual

Status: AWAITING_VERIFICATION. This manual describes executable assertions;
authored tests are not runtime evidence.

Sources:

- `test/01_unit/lib/io/piped_process_owned_v2_spec.spl`
- `test/01_unit/lib/common/build_manager/group_process_stream_protocol_v2_spec.spl`
- Native tests and their exact evidence are recorded separately in the design.

The new transport-only native witness passed on the recorded source snapshot:
[exact commands and hashes](piped_group_stream_transport_v2_evidence.sdn).
It does not qualify the Simple facade, compiled broker, or delegated cgroup
lifecycle. The six pure contract scenarios below remain NOT_RUN.

## Pure contract scenarios

1. Build one canonical owner and reference. Copy the reference, retain its PID,
   and independently change generation, group root, and identity. Each comparison
   must reject equality. An unchanged complete reference must compare equal.
2. Retain a valid owner whose launch deadline has expired. Owner validation must
   still succeed for cleanup; the separate signed lifetime remains unchanged.
3. Pair a valid owner with a different reference identity. Transfer validation
   must reject the mismatch before any native operation.
4. Change the retained request's memory limit without recomputing its admitted
   identity. Owner validation and cleanup must reject it before file/native effects.
5. Supply an already-assigned transport generation to owned spawn. It must reject
   replay before platform admission, registry reservation, or fork.
6. Compare complete transfers. Identical owner/reference pairs compare equal;
   another canonical request with a changed cache identity does not.

The protocol spec additionally checks independent argv digest bytes, canonical
round-trip, full positive i64 generation/deadline values, argv/digest mismatch,
deadline rejection, noncanonical encodings, V1 restriction preservation, portable
path shapes, and exact exec-ready/no-child receipt bindings.

## Native and service acceptance

The new native fixture must exercise the production registry and existing Linux
broker owner, not an alternate registry or mocked cgroup success. Verify exact
generation/binding, duplicate launch denial, old PID/ref adapter denial, sole
reader bytes/EOF, partial writes, wrong proof retention, and stale retirement.
Actual delegated cgroup execution must additionally prove descendant cleanup,
exec failure with retained lease, launch expiry before exec, descriptor inheritance
allowlist, broker diagnostics isolation, no-child admission proof, and retained
collected evidence across publication failure.

A missing writable delegation is an unavailable capability result, not a passed
positive lifecycle test. Windows owned-stream execution remains separately
unqualified; legacy Windows reference behavior is unchanged.

Use private artifact directories, finite timeouts, and shared CPU affinity 0-4.
Never repeat the earlier V1 registry selfcheck as evidence for this V2 feature.
Retained uncertainty consumes a bounded registry slot; never bypass cleanup or
reuse its generation to make a fixture pass. Successful cleanup retires the ref
but leaves durable owner evidence until the host ledger acknowledges its bound
`GroupedReapReceiptV1`. EOF, grant expiry, cancellation acceptance, and cleanup
success alone are not host capacity-release acknowledgement.
