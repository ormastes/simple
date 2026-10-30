# Bootstrap default source-to-object scheduling

Status: implementation plan; no default capability or successful build claimed.

The user selected cached source-to-object work per ready unit as the default
for Phase 3 and Phase 4, with 24 jobs and independent failures collected to the
end. A whole-tree HIR pass followed by whole-tree MIR and object passes is only
an explicit alternate mode. This requirement does not relax cache validation,
global language semantics, resource admission, or compiler lineage gates.

## Current boundaries

`driver_orchestration.spl` loads the source inventory, parses and lowers HIR,
then performs global semantic and specialization work before MIR/native output.
`SIMPLE_NATIVE_GROUP_MANIFEST` restricts the requested source members but still
uses this pipeline. `SIMPLE_MIR_SELECTIVE=1` consumes an already sealed post-mono
bundle; its explicit-native eligibility excludes the bootstrap route. Neither
is a source-to-object default scheduler.

Release inspection at `ff0513e624a` includes PR #4348's
`native_build_focused_capsule_shards_v1` in `native_build_main.spl` and
`bootstrap_capsule_shard_prepass` in `bootstrap_main.spl`. That route runs a
HIR shard prepass, then MIR/codegen shard work, then the focused in-process
capsule/final link; it also retains explicit in-process fallbacks. It is a
phase-batch compatibility route, not the requested per-ready-unit
source-to-object default. The cache/shard fixes may be useful for constructing
a future capable producer, but they do not satisfy REQ-SOBJ-001 or justify a
capability/default PASS. Existing shard opt-outs remain independent switches;
they are not new public HIR/MIR stop-output modes. Integration must rebase and
review these changed CLI boundaries without editing a live frozen compiler.

The unmerged HIR object frontier exposes `SIMPLE_HIR_OBJECT_FRONTIER_DIR` and
`SIMPLE_HIR_OBJECT_FRONTIER_JOB`. Its closed, nongeneric, no-call subset is an
initial worker capability, not sufficient bootstrap coverage. It must not be
advertised as the default full-compiler implementation.

## Required execution contract

1. Freeze the complete original source inventory, entry flags, producer bytes,
   runtime/provider identities, target, ABI, options, and declaration order.
   Build one immutable global declaration/interface index. Reading headers and
   sealing the index is allowed; retaining every lowered body is unnecessary.
2. Establish dependency strongly connected components and specialization demand
   closure. A unit becomes ready only when its interface, referenced bodies,
   method/trait resolution, storage authority, AOP/instrumentation inputs, and
   generic demand are sealed. Unknown dependencies block that unit with a real
   reason. They do not authorize synthetic declarations or changed entry roots.
3. A ready unit's owned process consumes frozen inputs and completes source
   parse, HIR, MIR verification/borrow/native passes and object publication
   before taking another unit. It owns mutable arenas and cache staging paths;
   transport contains immutable manifests and bounded results, never compiler
   pointers. A unit may use a validated cached object instead. The parent also
   reuses a valid library or final binary with a complete current receipt,
   selecting the furthest valid artifact instead of rebuilding it from a lower
   cache layer.
4. The coordinator admits processes using fresh memory/commit/disk headroom.
   The selected backend job budget is 24; this does not authorize 24 large HIR
   processes. It schedules ready work until each independently runnable unit is
   terminal, retaining failures and blocking only their dependent units.
5. Publication is transactional: immutable body/object bytes first, receipt last.
   Receipts bind full context, source/dependency/body digests, specialization and
   declaration authority, macros, aspects/instrumentation, generated inputs,
   relevant environment effects, post-pass MIR digest, object digest and actual worker
   exit. Codec failure refuses persistence and remains visible evidence.
6. The final parent validates current context and every post-pass MIR/object
   identity before deterministic assembly and linking. No copied/rekeyed cache
   record, changed per-unit entry closure, or aggregate guard bypass qualifies.

## Recipe integration ownership

The bootstrap recipe will select `source-object` by default and retain an
explicit `phase-batch` override. Cache use defaults on without an enabling
option, including explicit HIR/MIR/object step requests; disabling it requires
an explicit opt-out. Configuration is SDN;
existing command/environment precedence remains explicit. The recipe must
consume a compiler capability that proves this complete contract, rather than
silently translate `source-object` into the existing whole-tree pipeline.
Do not publish a default switch while that capability is missing.

The unmerged pure request-policy draft models this opt-out as `cache_override: "off"`
and otherwise returns `cache_enabled: true`. A public cache opt-out and actual
executor wiring are still pending; the typed boolean alone is not proof that
any compiler process reads or writes the requested caches. Preserve the current
native cache directory option and select one public opt-out spelling when the
capable execution route is integrated, rather than add competing cache flags.

Normal snapshot preparation has a two-second end-to-end target. Measure from
the source-authority request through immutable snapshot availability, including
inventory selection/admission and source publication. Retain cold and warm
measurements separately, but do not exempt cold preparation from the requested
normal-flow target. Reuse immutable inventory/snapshot authority where valid,
invalidate changed sources and dependencies precisely, and preserve fail-closed
checks. The observed campaign preparation (about 6m51s cold inventory plus
4m55s snapshot/admission) fails this target; no performance PASS is claimed.

Compiler execution and authority ownership stays with the execution lane;
the earlier frontier owner supplies interface continuity. The recipe/CLI lane
owns recipe/config integration, dependency/SCC readiness, deterministic terminal
commits and process documentation. The held a3ea
compiler campaign inputs remain immutable. Parent Hello success is required
before a dependent provisional generation, and formal admission remains distinct.

## Acceptance evidence required before landing the implementation

- Actual overlapping work shows unit A's native object committed while another
  independently ready unit still has source/HIR/MIR work outstanding.
- An injected real unit failure retains successful sibling objects and all
  independent terminal outcomes; link fails when a required object is missing.
- A second unchanged build reports validated cache hits without re-lowering
  those units. Source, dependency, producer, target, runtime, instrumentation,
  specialization, storage, macro, aspect, generated-input and relevant
  environment changes invalidate their affected proofs. An unchanged valid
  library or final binary is reused directly, with actual artifact bytes checked.
- Cross-unit calls, mutually dependent types, traits, imported private aliases,
  generics, original entry flags and global storage match the explicit phase
  pipeline in native executable output, not just policy booleans.
- Actual 24-job execution retains resource and cleanup receipts. Phase 3 then
  compiles/runs Hello; Phase 4 uses those exact immutable compiler bytes and
  subsequently builds its full CLI/test runner before suite claims.
- The explicit alternate mode is observable; an unsupported producer fails
  closed rather than secretly running phase batches under the default label.
- Cache is used without an enabling option; an explicit opt-out suppresses
  reuse/publication only for that request. Normal snapshot preparation meets
  the two-second complete-operation target with source/context invalidation
  negative controls and retained cold/warm timings.

These checks are pending. No full source-to-object default scheduler was found
in the inspected release revision `ff0513e624a`. The policy, graph and contract
drafts described here are unmerged work; this documentation does not enable
them or establish their runtime correctness.

## Explicit modes and initial producer construction

Preserve `--mode dynload|one-binary` as artifact/build packaging selection.
Preserve current native output choices `--emit-object`, `--emit-entry-object`,
`--emit-archive`, `--emit-shared` and their mutual exclusion. They are not
scheduler choices. The inspected native-build CLI currently has internal HIR
and MIR shard arguments, but no supported public HIR/MIR stop-output contract;
do not advertise an internal shard selector as a stage-output implementation.
Use one independent pipeline selector for source-object versus the explicit
phase-batch override; stage-output options must be bound to actual producers
and validated output receipts before adding their public spelling.

The existing immutable 88f3 Phase 2 compiler cannot acquire this feature from
a wrapper flag. Capability negotiation must reject it for the new default.
If a new capable producer must first be built using the explicit phase-batch
override, retain that exact argv, producer/source/runtime identities and the
reason in a separate construction receipt. Such construction is not evidence
that the default scheduler worked. After construction, run the exact new
producer's Hello gate, then build and qualify Phase 3 and Phase 4 with the
actual default source-object route, cached unchanged retries and native
execution. Rebuild Phase 2 instead when the lineage/admission policy requires
the feature in that producer; never relabel an old compiler as capable.
