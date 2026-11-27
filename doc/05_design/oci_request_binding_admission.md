# OCI request binding admission

Status: source admission, runtime checks **UNEXECUTED**. Starting release commit:
`e97e23b68b01d8c6e3634616d5fde7a1f1cbdf4d`. The existing Linux OCI provider
remains the effect owner. This slice adds no CI entrypoint behavior, runtime
framework, attach, storage, mount, environment, or terminal execution feature.

## Source provenance

Identified sources were read from the unrelated dirty `/home/yoon/dev/simple`
worktree; that worktree was preserved. Three data modules and the retained
request codec were admitted, with surgical provider binding hunks. Original
source SHA256 values before admission are:

| Source | SHA256 |
| --- | --- |
| `src/lib/nogc_async_mut/container/providers/linux/request_v1.spl` | `a97ab32dc5bac7da0e78083c084f9157d76e5c013bfb5a54935f084bad2437d3` |
| `src/lib/common/contracts/container/execution_options_v1.spl` | `65f00098b9ac13105f9e0ddc7b85ef9b7b233375005e23fcd5ccc2d6f05c6a2a` |
| `src/lib/common/contracts/container/bound_intent_v2.spl` | `b1eeb93709b3469c18057c7481967e87f822b0ba7231f28830640efa8083676f` |
| `src/lib/nogc_async_mut/container/providers/linux/request_codec_v1.spl` | `c4f747587f9da9fcf98e1c3ebd81ed7f13e445f9b08c597a5cf0224d735cb7a1` |
| Provider source material, **not copied wholesale** | `0f0a0d912b2f29193e2a929d3aa64635a6299433cdad940067899f5b3262145b` |

`request_v1` additionally rejects NUL in execution fields before hashing or
logical preparation. Supported payloads retain the identified digest field
order, version defaults, per-field hashes, and explicit vector counts.
`operation_id` is checked as ownership metadata separately from payload digest.

## Admission and durability

Preparation pins a bounded request digest and operation identity. Create checks
both memory and disk before returning cached success. The owner lease covers
reconciliation, intent publication, and the native create call. Every subsequent
effect/replay hashes the bounded request again and rechecks retained authority;
the writer rereads canonical disk authority under its stable writer lock.
An accessor cannot replace a cached digest/operation with conflicting disk data.
Eviction removes a destroyed state's binding together with its state and intent;
durable tombstones remain on disk.

New records use canonical SDN `RuntimeBoundIntentV2`. Unknown, unreadable,
noncanonical, foreign-scope, or mismatched records fail closed. A missing answer
from an existence probe is provisional: first publication writes a complete
0600 owned `.pending` record and uses `file_publish_noreplace`, so a dangling
symlink or any existing entry cannot be overwritten as an absent journal.
Known V2 transitions use atomic replacement only after canonical reread. File
bytes and the state directory are flushed before persistence succeeds; a failed
directory barrier retains written authority and prevents native create.

The caller must supply a trusted directory tree. These path-based primitives do
not establish race-proof handle-relative authority against hostile ancestors.
Only the attempt's exact `.pending` staging path is removed. No directory scans,
shell commands, broad deletion, or runtime pruning are introduced.

## Legacy migration

V1 records contain identity and phase without request-payload proof. They reject
prepare, create, start, and other new execution. A separate strict private V1
reader supports recover, inspect, stop, and destroy only when retained identity
matches scope, operation, labels, generation, and boot and names a full 64 digit
lowercase hexadecimal native ID. Names, partial IDs, absent IDs, and `--all`
never authorize legacy cleanup. The ordinary bound recovery discovery path can
still inspect its generated scoped name and validate native labels.

Legacy cleanup writes V1, retaining identity and allowing only stop/destroy
transitions. It cannot promote an unproven caller payload into a V2 digest or
resurrect a destroyed attempt. Bound cleanup retains its existing digest.
All native-ID command builders now reject a leading `-`; ordinary short IDs
remain supported for bound callers. The full hexadecimal restriction is limited
to legacy reconciliation.

## Data does not authorize effects

The request codec preserves complete canonical request bytes and digest for the
host's subsequent retained-request consumer. Encoding/decoding is data-only.
The additive `replace_entrypoint`, environment, working-directory, and terminal
fields participate in payload identity, but nondefault values explicitly reject
in provider validation and standalone create construction until their effects
are admitted. Default callers keep the existing command mapping and build-mount
behavior. The later command slice remains parked under
`build/oci-request-binding/parked-command/` with its owned diff.

## Evidence and limits

Authored cases: 26 existing provider cases updated for bound replay, 14 new
binding/migration cases, and 4 retained-request codec cases. All 44 are
**UNEXECUTED**, not a passing test count. Exact scripted argv fixtures exercise
real provider methods; explicit journal persistence opt-in exercises the real
writer with scripted effects. `executor_call_count` counts every executor entry,
including unmatched commands; negative assertions do not confuse fixture cursor
consumption with absence of effect attempts. Capability/version probe processes
are outside that counter.

Podman and an admitted self-hosted runtime are unavailable. Compiler/lib/MCP
checks, SPipe execution/docgen, live pinned-image conformance, startup latency,
request latency, and RSS evidence remain blocked. No runtime qualification,
power-loss durability experiment, performance target achievement, or production
readiness PASS is claimed.

## Shared diagnostic fixture (blocked)

`test/fixtures/orchestration/oci_binding_admission_fixture.spl` holds the seven
public request/identity/record/argv/filesystem helpers and two critical flow
checks shared with the binding unit spec. It imports no `std.spec`; builtin
assertions abort on unexpected results. The unit scenarios retain their original
assertions through these shared checks, covering changed payload rejection before
any executor entry and V1 exact-identity recover/inspect/stop/destroy with real
journal writes, stopped/destroyed V1 bytes, and no fabricated V2 binding.

`test/fixtures/orchestration/oci_binding_admission_native_probe.spl` invokes those
two checks as a tiny direct diagnostic. It is **BLOCKED / UNEXECUTED**, with no
build slot consumed. The supervising lane reported that the existing `afae`
producer already failed `secure_memory.fill_span` twice; the request digest's
SHA256 dependency reaches the same secure-memory closure. Repeating that known
unchanged producer failure is not new evidence. No diagnostic build or execution
was attempted in this worker. These source artifacts add no runtime qualification
or production readiness claim.

## Follow-up executable mode source admission

The subsequent command slice is documented in
`doc/05_design/oci_command_entrypoint_admission.md`. It admits the already-bound
`replace_entrypoint` execution mapping and CI request selection without changing
the foundation's schema/digest or journal rules. Foundation-era statements that
this specific effect is refused describe the preceding foundation boundary;
environment, working-directory, and terminal effects remain refused. Runtime
validation remains blocked/unexecuted in both slices.
