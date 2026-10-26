# Consumptive source and AST handoff under frozen SCV authority

<!-- codex-design -->

Status: proposed design for root review; no implementation or qualification.
This refines W3/W4 of [incremental build metadata](../incremental_build_metadata_20261008.md).
It does not reopen the closed closure-reuse, scope-context, or partial-export
verification cycles. Their limitations remain prerequisites, not assumed fixes.
The requested0.1-second single-SPL target remains unmeasured.

## Observed boundaries

References below are current-source locations captured2026-10-12.

| Owner | Actual behavior | Consequence |
| --- | --- | --- |
| `app/io/_CliCompile/native_build_closure.spl:301,382` | Captures frozen entry/root paths and discovers imports through the shared scanner | SCV admission and dependency discovery must remain authoritative |
| `compiler/80.driver/driver_source_loading.spl:772-801` | Global physical-path maps retain text, imports and sibling rows; misses read and scan bytes | Map lifetime, not just read API, controls reuse |
| `app/io/_CliCompile/compile_targets.spl:1285,1331` | Releases maps before either driver branch | Driver can reread previously discovered frozen sources |
| `compiler/80.driver/driver_source_pipeline_loading.spl:905-972` | Assigns source list, explicitly copies physical text once into owner vectors, computes identities and releases scanner maps | Removing CLI release alone does not establish safe ownership or bounded overlap |
| `compiler/80.driver/driver_source_pipeline_parsing.spl:369-406,868-935` | Selects frozen source owners and deduplicates parsed physical sources/aliases | Preserve current canonical source selection and poisoned-source handling |
| `compiler/10.frontend/frontend.spl:166-222` | Hashes transformed parser bytes and policy, loads encoded flat pools, reconstructs using parser text; publishes current provenance | AST cache hits still require source text; a raw-file digest is not a parser key |
| `compiler/10.frontend/frontend_parse_cache.spl:65-106` | Memoizes ambient scope and uses a flat key path | Concurrent request authority is not established by this owner; the held context proposal is not admitted |
| `compiler/80.driver/action_graph/artifact_service_bridge.spl:41-65` | Constructs a fresh `ArtifactServiceV1(profile, [])` per route | Its local claims do not establish one producer across independent requests |
| `app/cli/native_build_worker.spl:78-87` | Opens existing environment-variant handoff then calls the same CLI compilation owner | Preserve authenticated policy transport and use the same source handoff interface for standalone and worker |

The explicit text copy is a correctness workaround for native source ownership
and ABI failures; deleting it is not an optimization with established safety.
The current closure already has discovered-at-enqueue and resolver caches.
This proposal does not add redundant graph memoization.

The closed diagnostic packet `build/native_probe/entry-closure-owner-qualification-20261012`
provides no qualified native performance comparison. Its first two attempts
had mixed JIT provenance; its third never executed source. The root's distinct
`aggregate-native-f2-20261012-root` observation at22:56:59 showed a438-second
live interval,106.06s CPU,365,506,560B RSS and no compiler stage output after
the workaround banner. Terminal root evidence then recorded495.604s, timeout124,
Job0, sampled peak750,412KiB, no objects/executable and unchanged19,244 source
files plus producer/runtime pins. See that packet's `FAILURE_ANALYSIS.md`,
`RESULT.json` and `REQUEST.json`. This is a failed full-foreground experiment;
sparse output does not isolate SCV, scanner or cache latency. Current/frozen
source inspection does not identify which functions are embedded in that
producer. Do not substitute fake SCV admission to make the experiment faster.

## Decision and staged scope

S1 replaces the discovery-to-loading ownership boundary with a request-owned
source payload owner. It avoids rereading already admitted physical sources.
It does not promise no rereads during SCV snapshot creation/verification.
S2 adds shared immutable parser artifacts with a real serialized flight owner.
Neither stage shares mutable `ParserModule`, HIR, symbol tables or flat pools.
S3, deferred, could avoid fetching raw bytes for certain warm requests; current
pool reconstruction requires parser text, so a header or raw digest alone
cannot implement S3 safely.

A same-process S1 prototype is the smallest plausible change. Cross-process
S2 transport, global cache-context replacement, native ABI copy removal and
default header-only activation are outside that first patch. No production
change is safe to apply before native ownership transfer is demonstrated.

Native primitive feasibility has bounded evidence at
`build/native_probe/source-slot-native-feasibility-20261012/REVIEW.md`: an
expected clear-only negative and six positive cases passed once across two
cycles against the exact final3 core-C provider. Explicit-copy cleanup and
post-free destination bytes passed, including317,440-byte UTF8 and32aliases.
This does not qualify driver transfer, ABI, concurrency, RSS scaling or latency.

## Authority and identities

Use existing `ScvCompileSnapshotV1`, source-inventory binding validation and
the `compiler_source_authority_*_v1` adapter. Do not invent a second snapshot
authority or treat an exported `valid: true` field as proof. A driver-facing
binding contains validated snapshot identity plus source-inventory digest,
generation, canonical absolute roots and parser/environment policy identity.
Its constructor is owned by the validated admission path. Driver code must
not import the application authority owner in reverse.

Resolve roots once against an explicit absolute base. Reject paths outside
the admitted inventory, ambiguous physical identities, malformed digests and
invalid leases. Later CWD or environment changes cannot retarget a captured
binding. Inventory content hashes bind raw bytes, not timestamps. A snapshot
pins its old generation across edits; a new request admits a new generation.

Source slot key: snapshot/inventory binding + canonical physical identity +
expected raw digest. Module spelling and authored diagnostic paths are alias
rows referencing the slot; they cannot cause another payload copy.
Parser artifact key: exact transformed bytes + existing parser policy key +
grammar/codec/producer compatibility + every parse-affecting provider input.
Use the existing frontend key/frame owner; do not replace it with raw SHA.
Target/runtime/aspect/capture changes invalidate the stages they affect, and
must never inherit object compatibility from a parser-artifact hit.
Feedback-enriched parser artifacts remain uncached as currently required.

## Proposed interface, pending review

Proposed names are interfaces to review, not implemented exports:

| Surface | Role |
| --- | --- |
| `FrozenSourceHandoffBindingV1` in a common compiler contract | Immutable validated-binding description; consumes existing SCV/transfer vocabulary |
| `DriverSourceInputOwnerV1` in `80.driver` | Sole mutable owner of bounded physical source slots, aliases and phase state |
| `driver_source_input_owner_open_v1(binding, limits)` | Opens only after SCV admission; no ambient lazy initialization |
| `driver_source_input_scan_v1(owner, admitted_path)` | Reads/digest-checks/scans once into a slot, or lends a scoped read view |
| `driver_source_input_prepare_v1(owner, ordered_paths)` | Validates exact ordered closure and alias projection, reserves a transfer generation |
| `driver_source_input_adopt_v1(driver, owner, transfer)` | Owner-side validated consume into the driver; invalidates sender access |
| `driver_source_input_abort_v1(owner)` | Idempotent release on failure/cancellation; never publishes partial readiness |

Do not expose raw pointer handles or disguise a copied record as a moved owner.
Use the existing `ParallelTransferMode.OwnedMove`, `ScopedLoan`, `FrozenShare`
and lease vocabulary. The current provider must prove the selected transfer
mode; unknown mode is rejected. No process-global mutable map is introduced.

Ownership classification requires the actual producer contract. Returned text
may alias its input even when large: tested core-C `rt_string_repeat(v,1)`
returns `v`. Neither length nor `OwnedMove` identifies exclusive allocation.
Explicit zero-offset substring copying creates an independent allocation for
the tested nonshared values; empty/one-byte copies are process-shared and
correctly refuse freeing. Those rows require `FrozenShare`/loan treatment,
without claiming a successful free. A copy/loan fact must travel with the
owner generation rather than be reconstructed from a text handle later.

The current CLI API remains compatible. Both normal and emit_smf branches
capture one owner after admission, pass it to a handoff-aware driver factory,
then use the existing collection-profile wrapper. Standalone captures its
private authority through the existing adapter; the build worker first opens
its existing authenticated policy handoff and follows the same driver path.
Direct callers without a handoff use the current validated source-loading
path. There must be no half-enabled mode that skips validation or drops inputs.

Narrow patch outline: introduce the common binding and driver owner; adapt the
scanner to an explicit owner; extend closure discovery to return its ordered
paths plus owner transfer; add a handoff-aware driver constructor; consume in
loading; preserve the old public wrappers. Parser changes are unnecessary for
S1. Keep final native action inputs and final toolchain revalidation intact.

## Ownership and peak-memory invariant

States: `Open -> Prepared -> InTransit -> DriverOwned -> Released`;
failure/cancel reaches `Released` from any nonterminal state. Only the current
owner and generation may advance the state. Prepare does not publish source
inventory or give the destination access. Destination validates before commit;
failed adoption drains the transfer without reviving sender access.

Discovery slots are the canonical raw-byte owner from the first admitted read.
Scanner loans end before adoption. Driver inventory stores slot references and
small alias metadata; it must not retain a second full-body vector. If native
ABI isolation still requires copying, copy one physical slot at a time and
release its old payload immediately after successful destination validation.
Peak transfer overhead is then bounded by one largest source plus bounded
metadata, rather than another whole input heap. This bound is a requirement,
not proven by assigning `text` or clearing one dictionary.

`ctx.sources`, `all_sources`, scanner maps and parser-owner vectors must all be
included in the alias audit. Replacing one map while other aliases retain its
texts does not consume ownership. Any unsupported provider keeps the existing
copy/read fallback and reports it; no memory improvement is claimed there.
Large sources need admitted streaming/spill or existing correct fallback;
never truncate a valid input to fit the transfer budget.

After parse, keep source/spans until the last required diagnostic reader joins.
Mutable flat-pool restore is worker-local. Encoded AST artifacts are immutable
leased bytes; each worker restores its own mutable pool, unless a separately
qualified frozen AST representation proves immutable sharing. Bound decoded
artifact bytes and active parser tasks, not only task counts.

## Concurrency and publication

S1 ownership is one request in one execution domain. It does not by itself
guarantee no duplicate producers across processes. S2 needs one existing
service/coordinator owner shared by all adapters, with serialized claim,
complete, cancellation and lease-generation transitions. A new route-local
`ArtifactServiceV1` is not that owner. The local standalone adapter embeds the
same service interface; independent processes claiming a shared cache require
a qualified cross-process owner/lock or remain explicitly outside sharing.

Flight key identifies a stage artifact, not just a module name. One producer
owns an epoch; waiters hold bounded leases, release CPU credits and never
retain duplicate payload copies. Publish only an authenticated complete blob
after syntax/codec validation and atomic commit. Stale epochs cannot publish.
Producer death drains its claim before one replacement is admitted. Cyclic
imports use existing SCC ordering; a waiter cannot consume the producer's last
scheduling credit and deadlock the graph. Deterministic owner commit order is
independent of completion order.

Syntax errors remain failures, not empty AST hits. Optional negative results
must bind exact source/parser/policy identity and preserve complete diagnostics;
otherwise do not cache them. Invalid/corrupt AST data is a real parse miss.
An invalid or missing source authority fails before reuse, rather than falling
back to unvalidated live files. Failure and cancellation release every lease.

## TLDR and object boundary

Preserve name-atomic partial-export metadata, authenticated omitted names and
preflight before binding mutation. Missing names, unsupported requested names,
glob/global/dynamic cases route to the required source body. Unused unsupported
exports alone need not force all bodies. Header readiness does not establish
generic-body, inline/CTFE-body or native-object availability. A header-only
request still schedules and authenticates all required canonical object
dependencies. No object digest may be inferred from a successful AST restore.

## Observability and qualification

Emit monotonic stage start/end boundaries for process entry, source admission,
inventory verification, snapshot materialization, closure scan, owner transfer,
parser-key transformation/hash, cache validation/restore, real parse, HIR,
object production and link. Start markers precede potentially blocking work.
Separate bytes read by admission, compiler source, AST cache, toolchain and
external pin/collector wrappers. Attribute cold/warm wall, CPU and memory to
measured intervals; absent boundaries mean unattributed time.

See the [acceptance plan](../../03_plan/sys_test/scv_consumptive_source_ast_handoff_20261012.md).
Runtime evidence must identify immutable producer/source/runtime/tool pins,
actual execution mode and complete read provenance. Source-only tests establish
algorithmic behavior only. They do not admit native transfer, worker ABI,
whole-foreground latency or memory claims. Unit tests are not formal proof.
Full-CLI admission additionally requires a compiled worker with the reviewed
handoff actually embedded, real source/runtime/toolchain provenance, successful
native output and execution. Merely placing changed source beside an older
producer does not satisfy that requirement.

## Owners and implementation hold

`compile_targets.spl`, `driver_types.spl` and
`driver_source_pipeline_loading.spl` are dirty under root/other lanes.
`driver_source_loading.spl` was clean during this review; that does not grant
ownership of its downstream consumers. No production edit is proposed for
immediate application. Root coordinates exact hunks with those owners first.
The explicit driver copy and held cache-context work are blocking proof gaps.
Lower-model sidecars: N/A, focused ownership design. Integration/merge owner:
root. Final semantic/ownership reviewer: root/Astra. No remote action here.
