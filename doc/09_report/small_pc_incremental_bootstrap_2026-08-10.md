# Small-PC incremental bootstrap verification — 2026-08-10

STATUS: FAIL (verification resource-blocked)

The Cargo worker propagation contract passed and live Rust authority builds ran
with one worker. A single optimized rustc still peaked near 3.5 GiB RSS.

Three bounded Stage3 trials were performed against the retained cache:

1. Positional low-memory activation peaked near 5.7 GiB, avoided an OOM kill,
   but reported one HIR failure after parsing 836 modules.
2. The established non-streaming control was killed by the kernel (exit 137).
3. Explicit Stage3 streaming-surface admission was also killed (exit 137) after
   source closure/load, before parse progress, at approximately 5.7 GiB RSS.

The dominant allocation therefore occurs during or before source-closure/load,
earlier than the existing streaming parse/reclaim boundary. The resumed fix
moves each source's text import scan into a transient scope and promotes only
module paths retained by closure state. Acceptance is pending a new bounded
bootstrap cycle.

Stage4 was unavailable. No binary was deployed and nothing was pushed.
Evidence is retained under `/home/yoon/simple/build/bootstrap/logs/` and
`bootstrap-build-progress.events`.

## Resumed closure-scan fix — 2026-08-11

Per-source transient closure-import scanning reduced the measured completion
RSS from about 5.7 GiB to 2.24 GiB (roughly 60%). The first run was later OOM
killed at about 4.34 GiB while an unrelated native build was consuming memory
and swap. A clean retry exposed a missing persistent-owner promotion as a
segfault after the first streaming surface release; all mutated closure owner
graphs are now promoted before scope teardown.

The final validation run was paused when another unrelated 2.7 GiB Simple build
started. That build filled all 4 GiB swap and remained CPU-active beyond the
bounded wait window. The paused Stage3 was terminated cleanly with exit 143 to
avoid destabilizing the host. The final owner-promotion change therefore still
requires one uncontaminated Stage3-to-Stage4 run. It is not deployed or pushed.

## Final bounded cycles — 2026-08-11

Narrowing promotion to the compact import-path result reduced Stage3
closure/load RSS again, from 2.24 GiB to approximately 0.76 GiB. Persistent
mutations now occur outside transient ownership and no closure lifetime crash
was observed.

Disabling declaration arenas only for explicitly streaming Stage3 delayed swap
growth and produced repeated per-file RSS reclamation (about 0.56–5.3 GiB), but
streaming HIR eventually accumulated to about 5.8 GiB after ten minutes, filled
the 4 GiB swap device, and was kernel-killed with exit 137. The remaining owner
is accumulated HIR/retained surface material during phase 3, not source closure,
Cargo concurrency, or global configuration.

That resumed three-cycle limit was exhausted. Stage4 and deployment remained
unavailable; later reviewed increments were published only to the dedicated
feature bookmark, never to `main`.

## Transient parser ownership cycles — 2026-08-11

Durable phase profiling disproved retained source text as the dominant owner:
closure load completed at about 451 MiB RSS for 847 logical / 573 physical
sources. The first rich surface parse then raised RSS into the multi-GiB range
while the registered-heap count changed only slightly.

The bounded fixes now:

- construct compact surfaces inside the active transient scope, promoting only
  the completed surface before publishing persistent builder state;
- keep declaration arenas out of the leaking per-field environment mirror;
- free the transient raw-allocation side table above its bounded capacity and
  trim returned glibc pages;
- reset persistent parser arenas while the scope is paused, releasing their
  backing capacity while preserving their persistent owners; and
- lower HIR before pausing, promoting only the reduced registry, diagnostics,
  entry HIR, and explicitly preserved cross-module lowering state.

The first combined run advanced from two released surfaces to twenty before an
exit-137 kill. After allocator trimming, it still reached roughly 6.0 GiB during
the first surface. Releasing paused arena capacity reduced the next run to about
4.35 GiB after two surfaces, but RSS then rose to about 6.15 GiB during the third
parse and the kernel killed Stage3 (exit 137). This is real improvement but not
acceptance: Stage4, deployment provenance, and exact-binary smoke remain absent.

The reviewed incremental fixes are published only on the dedicated
`bootstrap-smallpc-memory` bookmark. `main` remains unchanged until the full
bootstrap and deployed-binary gates pass.

## Allocator-order and interface-projection probes — 2026-08-11

Trimming only while the transient raw side table was freed happened before
persistent parser-arena backing arrays were released. A follow-up deferred the
glibc trim until scope end, after both ownership classes were reclaimed. The
focused ownership contract remained 11/11, but live Stage3 still reached about
6.0 GiB RSS after two released surfaces and was killed with exit 137.

An A/B probe with one glibc arena, zero trim threshold, and a 16 KiB mmap
threshold reached 6,373,844 KiB max RSS and was also killed. This disproves
ordinary glibc arena fragmentation as the dominant remaining owner.

A final bounded experiment parsed the existing fail-closed interface projection
instead of ordinary function bodies for trait-free surface modules. After
making removed bodies syntactically valid with indented `pass` stubs, Stage3
again reached about 6.0 GiB after the same two surfaces and was killed. The
experiment was abandoned rather than published because it provided no measured
memory improvement. The remaining defect is a large per-file parser allocation
floor outside the registered heap count and independent of ordinary body text.

## Discard-only parser arena cycles — 2026-08-12

A runtime audit established that the prior transient scope was an ownership
tracker, not an allocator: raw parser allocations still used libc `malloc` and
populated a potentially multi-GiB open-addressed side table. A separate,
non-promotable mmap bump arena now owns raw parser scratch. The driver pauses
that arena after parsing and constructs the persistent `ModuleSurface` only
after the pause, so scope end can unmap parser scratch without evacuating or
dangling retained values.

Three bounded live cycles were run with one worker and the retained cache:

1. Raw arena isolation reduced the same two-surface checkpoint from roughly
   6.0 GiB to 4.35 GiB, but the third source was killed with exit 137.
2. Propagating arena release into the post-scope glibc trim reduced that
   checkpoint again to about 2.2 GiB; the third source reached about 4.35 GiB
   before another exit-137 kill.
3. Routing scope-owned boxed headers and array/dictionary backing storage
   through the discard arena preserved the 2.2 GiB checkpoint, but the third
   source still rose past about 4.1 GiB and was killed before release.

Focused evidence passed: core-C syntax, Rust `simple-common`/`simple-runtime`/
`simple-compiler` checks, and the 11-case streaming ownership contract. The
runtime capsule was blocked before its transient self-check by the existing
`runtime_coverage_core.o` undefined `rt_string_new` link defect.

The three-cycle cap is exhausted. Status remains **FAIL**: Stage3 did not
complete, Stage4 was unavailable, no candidate was deployed, and exact-binary
essential-tools/MCP checks could not run. The allocator changes are retained on
the dedicated `bootstrap-smallpc-memory` bookmark for review; they must not be
promoted to `main` until a subsequent scoped design addresses the remaining
single-source parser peak and all deployment gates pass.

## Compact arena follow-up — 2026-08-12

The next bounded continuation tested three narrower allocator hypotheses. A
reusable free-list arena was rejected after measurement because its per-object
metadata raised the third-parse peak to about 5.95 GiB. Replacing it with an
8-byte bump header plus in-place tail `realloc` still reached about 6.05 GiB and
was killed. Finally, sparse zero-filled allocation avoided eagerly touching
anonymous mmap pages, but the exact retained-cache bootstrap again released
only `bootstrap_main.spl` and `driver.spl` before Stage3 was killed (exit 137).

The focused core-C syntax check, transient-heap self-check, and 11-case
streaming ownership contract passed once for the retained compact/sparse
implementation. Source-order analysis also established that the next physical
source is the tiny 856-byte `driver_core_types.spl` facade, so source splitting
or ordinary body projection cannot solve the peak. The remaining failure is a
fixed parser/runtime allocation cost within one invocation, not source size,
worker concurrency, retained raw source text, or Cargo storage. Verification
therefore remains **FAIL**; Stage4, deployment, and exact deployed-binary smoke
were not reached, and no `main` push is permitted.

## Stage2 runtime authority correction — 2026-08-12

Three additional bounded cycles proved that the prior discard arena was wired
to the wrong runtime authority. Stage3 is executed by the Rust bootstrap
runtime, whose `rt_transient_discard_scope_begin()` explicitly delegated to the
ordinary malloc-tracking scope; the mmap implementation in
`runtime_native.c` is used only by the later core-C artifact. All three cycles
again reached the exact 856-byte `driver_core_types.spl` third source and were
killed near 6 GiB RSS.

The next source-matched fix adds a distinct, non-promotable discard arena to
`runtime_memory.c` and routes the Rust bootstrap runtime's discard API to it.
Pre-pause raw parser allocations now use zero-filled anonymous mappings without
growing the old raw-allocation hash table; post-pause retained surface
allocations remain ordinary persistent allocations. A dedicated C self-check
proves allocation, pause isolation, full unmap at scope end, and retained
post-pause data, and the streaming ownership contract remains green. The live
bootstrap gate is deliberately deferred to the next bounded continuation
because this continuation's three-cycle cap is exhausted.

## Stage2 owner isolation cycles — 2026-08-12

Three source-matched cycles exercised the new Rust-bootstrap discard API. The
first and third reached the unchanged third physical source and were killed at
about 6.08 GiB RSS. A second cycle added threshold counters for both relevant
runtime owners: raw discard mappings at 256 MiB intervals and scoped Rust heap
objects at 262,144-object intervals. Neither threshold fired before the kill.
`/proc/<pid>/smaps` instead showed approximately 6.1 GiB resident inside one
coalesced 8 GiB anonymous mapping.

A size-segregated recycler was added for freed raw parser blocks and its focused
two-wave reuse/unmap self-check passed, but the third live cycle retained the
same profile (about 4.34 GiB at 1:08 and 5.91 GiB at 1:52) before exit 137. This
disproves both the tracked raw-allocation table and Rust scoped heap objects as
the dominant remaining owner. The next bounded diagnostic must identify the
creator of the 8 GiB anonymous mapping (for example with a named VMA or an mmap
syscall trace against the admitted Stage2 binary) before another allocator
change. Stage4, deploy, and exact-binary gates remain unavailable; status is
still **FAIL**.

## Exact 8 GiB owner and frontend fix — 2026-08-12

A bounded syscall-stack replay of the exact admitted Stage2 transcript finally
identified the allocation owner. `mremap` grew one mapping from 4 GiB to 8 GiB
through `realloc`, `rt_array_push_grow`, and
`layer_eq_registry_reset_module`. The empty global annotation registry was
being rebuilt on every parser initialization; under the native authority its
empty iteration corrupted the rebuilt array length and caused geometric growth
to 8 GiB. The source-matched correction gives the layer-equality, effect, and
aspect registries authoritative scalar counts, returns before rebuilding an
empty registry, and updates the count after declarations and filters. Its
focused source contract passed once.

The first cache-preserving bootstrap after that correction passed the former
third-source OOM boundary and released 115 physical module surfaces before a
new deterministic alias error. A second diagnostic cycle reproduced that
error. The third cycle, after moving physical-source identity out of the
retained aggregate and into scalar builder dictionaries, released 42 surfaces
and reported the exact canonical source
`src/compiler/10.frontend/core/lexer.spl`; it did not exhaust memory. The next
source-matched diagnostic includes expected and actual content length/hash so
the alias mismatch can be corrected without weakening conflict detection.

This is material progress but not acceptance: Stage3 has not completed,
Stage4/deploy/exact-binary smoke remain unavailable, and verification remains
**FAIL**. The next live bootstrap is deferred because the mandatory three-cycle
cap for this continuation is exhausted.

## Alias identity comparison cycles — 2026-08-12

The next three cache-preserving cycles made the alias failure fully
falsifiable. Cycle one printed equal expected/actual identity values for the
lexer alias: length `34472` and hash `-242178392940823541`. Nevertheless, the
admitted native Stage2 evaluated the combined inequality as true. Splitting
the length and hash checks proved that length comparison succeeds but `!=`
mis-evaluates the two equal negative `i64` hashes. The focused canonical-path
contract passed all three examples after the split.

Cycle two reproduced only that negative-hash comparison failure. Cycle three
replaced it with ordered integer comparisons, but that source-matched Stage2
segfaulted during the second streamed parse, so the ordered form was rejected.
The pending correction compares canonical decimal hash text instead, retaining
exact conflict detection without either problematic signed-integer lowering.
It has not received a live bootstrap replay because this continuation's third
and final full cycle was already consumed. Verification therefore remains
**FAIL**; Stage3 completion, Stage4, deploy, and exact-binary smoke are pending.

## Physical-path and 735-surface frontier — 2026-08-12

The decimal-text hash correction passed the former lexer alias and restored the
115-surface frontier. The next error exposed an intermittent empty canonical
key from the hand-written `split`/array path normalizer. Replacing that scratch
normalizer with the existing `rt_path_absolute` physical-path authority moved
Stage3 to 735 released physical surfaces without OOM, then it segfaulted while
processing the following alias.

Removing redundant per-path content length/hash dictionaries produced the same
735-surface frontier and lowered the final heap-registry count slightly
(`9346513` to `9345479`), proving those dictionaries were not the crash owner.
The inline alias diagnostic was shadowed and emitted nothing, so the next
source-matched build now routes an alias marker through the working driver log
helper before mutating the alias index. The three-cycle cap is exhausted before
its live replay. Verification remains **FAIL**; Stage3/Stage4/deploy and exact
deployed-binary gates are still pending.

## Path-index and canonicalization isolation — 2026-08-12

Three further bounded cycles isolated the repeated post-`sffi_common.spl`
segfault. A helper-bound alias marker emitted nothing before the crash, proving
the failure precedes alias mutation. A per-candidate marker perturbed native
execution and crashed during the second parse, so it was removed as invalid
instrumentation. Replacing the physical-path dictionary with stable parallel
path/index arrays changed the same frontier from release sequence 735 to 574
(more aliases were recognized) and reduced the heap registry from about 9.35M
to 7.24M, but the next canonicalization still segfaulted.

Retained source-order evidence identifies the following source as
`src/lib/nogc_async_mut/path.spl`. The pending source-matched correction stores
the physical path once in `SourceFile` during phase-1 loading and propagates it
to aliases, so the streaming loop no longer repeatedly calls path resolution
at this high-cardinality frontier. The three-cycle cap is exhausted before a
live replay. Verification remains **FAIL**; Stage3/Stage4/deploy and exact
deployed-binary gates remain pending.

## Export candidate normalization — 2026-08-12

The reserved-prefix filter removed `SIMPLE_BOOTSTRAP_DECL_0_`, exposing a
second stale tagged slot rendered as numeric `1`. Calling text methods directly
on that tagged value caused an early signal, so candidates are now interpolated
to owned text before validation. That source-matched replay passed the early
signal, but native string containment incorrectly failed to recognize numeric
`2`, which again reached the ambiguity guard.

The pending correction replaces containment with ten independent scalar text
equality checks. Legal Simple export spellings cannot start with a decimal
digit, and independent comparisons avoid the already-evidenced combined
boolean lowering defects. Three full cycles are exhausted before live replay.
Verification remains **FAIL** pending Stage3/Stage4 completion, deploy, and
exact deployed-binary smoke.

## Authored export extraction and phase-3 admission — 2026-08-12

The source-backed per-candidate validator remained vulnerable to native text
equality and was O(stale slots × source lines), doubling the final registry to
about 13.48M objects. It was replaced with a single per-source pass over
authored `export` lines; the corrupt retained `ParserExport` array is no longer
read at all. This restored the registry to about 7.65M under the debugger and
completed phase 2 without an ambiguity or signal.

The exact debugger replay then exited with `phase 3 FAILED` before the first
HIR file marker. The first streaming-HIR admission lookup still used the native
compatibility `index_by_name` dictionary. The pending correction uses the
already-authoritative ordered name/index scalar arrays instead, matching the
successful physical-path lookup conversion. The initial full run, follow-up
full run, and debugger replay exhaust the three-cycle cap. Verification remains
**FAIL** pending live HIR replay, Stage4, deploy, and exact-binary smoke.

## Source-backed export validation — 2026-08-12

Three retained-cache cycles refined stale export-slot rejection without any
OOM recurrence. Independent text equality removed numeric `2` but exposed the
sentinel `-1`; rejecting hyphen then exposed numeric `5`. Byte-level ASCII
range checks reliably removed integer and sentinel debris, after which a stale
identifier-like value `compiler.` reached the ambiguity guard.

Lexical shape alone is therefore insufficient. The pending correction accepts
a compact export route only when its exact comma-delimited spelling appears on
an authored `export` line in that source. This validation runs during the
transient per-file build, before parser teardown, and rejects backing-array
debris without weakening legal export semantics. The three-cycle cap is
exhausted before live replay. Verification remains **FAIL** pending Stage3,
Stage4, deploy, and exact deployed-binary smoke.

## Export-origin crash ownership — 2026-08-12

The phase-1 physical-path field replay completed all 573 unique physical
surfaces and then segfaulted at the same boundary. Two exact admitted-Stage2
debugger replays proved this is no longer a parsing, path, dictionary, or memory
failure: the native stack is
`ModuleSurfaceBuilder.resolve_export_origins -> parse_all_streaming_surfaces_impl`,
with owner surface index `0`. Disassembly and registers show a valid exports
array returning a null first `ParserExport`, followed by an automatic
dereference of `export_decl.items`.

The pending source-matched correction skips nil export placeholders before
field access in all five ModuleSurface export traversals. Nil carries no export
semantics, so this is a fail-safe representation guard rather than a behavior
change. The continuation's full run plus two debugger replays consume the
three-cycle cap; live verification is deferred. Status remains **FAIL** pending
Stage3 completion, Stage4, deploy, and exact deployed-binary smoke.

## Compact export-route ownership — 2026-08-12

The nil guard passed its original crash but a debugger replay showed the next
retained `ParserExport` was non-null with a corrupt `items` pointer. Export
routes are now flattened to parallel scalar source/local/glob arrays during
surface construction, while parser objects are valid. Export-origin resolution,
fixpoint bounds, syntactic lookup, and registry freezing consume only those
compact arrays; retained parser export aggregates are no longer traversed.

The source-matched replay compiled this refactor and completed export-origin
execution without a signal. It then failed closed with
`ambiguous facade export: module=std.nogc_sync_mut.io_runtime item=2`, even
though that source declares no exports. This proves the flat bridge's nominally
empty export array retains stale native slots. The pending correction adds an
authoritative `ParserModule.explicit_export_count`, records it during flat
assembly, propagates it through desugaring, and flattens only that prefix. The
full run, debugger replay, and follow-up full run exhaust the three-cycle cap.
Verification remains **FAIL** pending its live replay and all later gates.

## Compact import routes and flat placeholder filtering — 2026-08-12

The authoritative export count passed the stale numeric `item=2` failure. The
next exact debugger replay moved the crash to
`module_surface_explicit_import_origin`, proving retained `ParserImport`
aggregates have the same lifetime defect. Import module/source/local/glob data
is now flattened before parser teardown, backed by an authoritative flat-bridge
import count, and all explicit/glob resolution plus freeze alignment consumes
those scalar arrays.

The source-matched follow-up compiled and ran this import refactor without a
signal. It failed closed on a textual export item named
`SIMPLE_BOOTSTRAP_DECL_0_`; this reserved flat-arena scratch placeholder had
leaked through an oversized retained export-item backing array. The pending
correction filters that reserved synthetic prefix while constructing the
compact semantic route. The full run, debugger replay, and follow-up full run
consume the three-cycle cap. Verification remains **FAIL** pending live replay,
Stage3/Stage4 completion, deploy, and exact deployed-binary smoke.

## Bounded-memory phase-2 success and HIR admission — 2026-08-12

Two source-matched, retained-cache runs completed all 573 unique physical
surfaces without OOM. The final phase-2 heap registry was approximately 7.65
million entries and sampled RSS remained about 733–750 MiB, replacing the
earlier multi-gigabyte growth and exit-137 failure. Both runs then returned
`phase 3 FAILED` before the first HIR file marker.

The HIR admission path no longer uses native dictionaries for physical-unit
membership. It now keeps aligned scalar index/module arrays, resolves canonical
sources by the exact phase-2 physical fingerprint, falls back to the aligned
name registry only for aliases, and validates aliases by canonical path plus
content identity. This also fixes the prior impossible alias check that required
an alias to have the physical surface's original source index and module name.

The third source-matched run rebuilt Stage2 successfully but terminated with
SIGSEGV (`exit-139`) while parsing the second phase-2 surface, before exercising
the corrected HIR admission path. The continuation's three-cycle cap is
therefore exhausted. Verification remains **FAIL**: Stage3/Stage4 completion,
deployment, exact deployed-binary smoke, and the compiler/lib/MCP acceptance
checks are not yet evidenced. The feature bookmark may carry the improvement
and evidence; `main` must not advance until a later continuation reaches PASS.

## Export-owner index OOM root cause — 2026-08-12

An exact Stage3 transcript replay under gdb completed all 573 streamed surfaces,
then the kernel OOM killer terminated `simple` during export-origin finalization:
`total-vm=12307444kB`, `anon-rss=6099896kB`. This isolates the remaining memory
spike after phase 2 rather than in the parser arena. The pass owned four global
native dictionaries keyed by newly formatted `package::declaration` strings.

Those dictionaries and combined keys are replaced by one fixed-capacity,
open-addressed `ModuleSurfaceOwnerIndex`. It stores package and declaration
identity separately in aligned scalar arrays, sizes once from declaration and
export-route counts, and preserves direct-owner, terminal-owner, collision, and
alias semantics. The focused Stage4 streaming ownership contract passes 12/12
under the bootstrap seed diagnostic. Full self-host acceptance remains pending;
this diagnostic is not Stage3/Stage4/deployment proof.

## Export-origin fixpoint dictionary growth — 2026-08-12

The first source-matched run with `ModuleSurfaceOwnerIndex` kept the post-phase2
pass near 750 MiB for several minutes, then was OOM-killed at
`anon-rss=6334884kB`, `total-vm=12305956kB`. A symbol breakpoint measured the
owner constructor input as 13,407 entries (capacity 32,768), ruling out owner
index oversizing. A separate replay reproduced the intermittent second-surface
SIGSEGV in `flat_ast_to_module`; the following replay reached the owner
constructor, confirming both outcomes are nondeterministic symptoms around the
same retained native state.

The remaining repeated-growth boundary was `ModuleSurfaceExportOriginIndex`.
Every fixpoint update still used native dictionary membership as authority; a
stale false miss appended a duplicate scalar origin and rewrote compatibility
dictionaries on every pass. Scalar `names` are now the sole update/lookup
authority. Compatibility `origins` and `index_by_name` dictionaries are built
exactly once during registry freeze, after the fixpoint completes. This
continuation's full run and two debugger replays exhaust its three-cycle cap;
live Stage3/Stage4/deploy acceptance remains pending and status is **FAIL**.

## Fixpoint temporary-text accumulation — 2026-08-12

The next retained-cache full run again completed all 573 surfaces near 750 MiB.
The post-phase2 pass grew more slowly after scalar origin lookup, reaching about
2.7 GiB after six minutes before the same kernel OOM terminal state
(`anon-rss=6352024kB`, `total-vm=12298112kB`). The remaining hot loop still
published compatibility origin dictionaries after every scalar update and
recomputed canonical/package names through allocating text transforms on every
surface and unresolved route in every fixpoint pass.

Hot-loop compatibility publications are removed; freeze remains their single
publication owner. Canonical module and package names are now computed once per
surface and reused by owner promotion and sibling resolution. The focused
streaming ownership contract remains PASS (12/12). Full self-host acceptance
is still pending the source-matched replay.

The source-matched replay held the entire fixpoint at approximately 732 MiB
with no virtual-memory growth, then jumped once to roughly 4.1 GiB RSS / 5.9
GiB virtual memory during registry freeze and was OOM-killed. This isolates the
one-time compatibility dictionary publication itself. All semantic lookup
consumers already use the aligned scalar origin arrays, so frozen surfaces now
leave the legacy `origins` and `index_by_name` dictionaries empty and validate
only scalar alignment. The next source-matched run is required for acceptance.

That run again stayed flat near 732 MiB through the fixpoint/freeze interval,
then accumulated to the same 6.36 GiB terminal RSS. With dictionary and text
construction removed, the remaining unbounded input is fixpoint pass count:
retained native text comparisons could repeatedly classify an already-recorded
origin as changed. Origin resolution is now a monotonic lattice. An explicit
import fills a missing slot or upgrades `plain-sibling` exactly once; an existing
sibling remains stable while the sibling resolver still fails closed on true
ambiguity. The three full cycles for this continuation are exhausted, so live
acceptance of the monotonic fix is pending and verification remains **FAIL**.

The first source-matched monotonic run still OOM-killed at 6.37 GiB after all
573 surfaces, with no HIR marker. This disproves repeated terminal-text updates
as the complete explanation. A bounded per-pass marker now records pass number,
changed state, and heap-registry count so the next run can distinguish a single
oversized pass from cross-pass accumulation without high-volume tracing.

The marker proved the first pass alone was the owner:
`pass=1 changed=false heap_registry=7727210`, while RSS had already reached
about 4.8 GiB and later OOM-killed at 6.37 GiB. Thus the scan was semantically
no-op for the current Stage3 closure but allocated enormous raw temporary state.
Stage3 streaming now treats the completed direct-origin pass as authoritative
and skips the compatibility-chain fixpoint. Stage4 keeps the general fixpoint
until its larger graph provides independent evidence. Live acceptance remains
pending the third continuation cycle.

The third source-matched run proved the environment-gated bypass did not
activate in the admitted native binary and again entered the measured no-op
pass, reaching about 4.6 GiB before OOM. Because the complete Stage3 graph
reported `changed=false` on its first compatibility pass, the direct origin
resolution is now unconditional authority and returns before the legacy scan.
The continuation's three full cycles are exhausted; verification remains
**FAIL** pending live replay, Stage4, deploy, and exact-binary checks.

The first source-matched run with the unconditional legacy-scan return still
OOM-killed before HIR. This corrects the remaining ownership boundary to the
initial direct origin-resolution pass itself. Eight bounded checkpoints (one
per 64 surfaces) now record direct-pass surface position and heap registry so
the next run can distinguish cumulative per-facade scratch from one pathological
surface without high-volume logging.

The markers localized the growth: direct surfaces 0–320 stayed near 731 MiB;
surface 384 remained bounded, but by surface 512 RSS had reached about 2.4 GiB.
Across all checkpoints the heap registry rose by only five objects per 64
surfaces, proving raw scratch rather than retained semantic origin graphs.
Streaming HIR already owns compact source/local/target route arrays, so the
legacy inferred-origin traversal is now bypassed entirely and origin hints stay
empty. Cycle 3 must validate whether any HIR consumer still depends on those
legacy hints.

Cycle 3 completed all 573 surfaces and then OOM-killed before the first direct
surface marker. Because that marker follows owner-index construction, the
remaining boundary is the owner-index build itself: native text/hash probing
over retained declaration names consumed 6.38 GiB without publishing an origin
graph. The streaming parser caller now proceeds directly from compact surface
extraction to `finish()` and never invokes `resolve_export_origins()`. The three
cycles are exhausted; live HIR/Stage4/deploy acceptance remains pending.

The first run with the streaming caller bypass still OOM-killed immediately
after surface 573. The exact remaining boundary is therefore `finish()` freeze.
Its alignment validator materialized complete compatibility dictionary key and
value arrays before target construction, despite aligned scalar names/indices
already being authoritative and checked at insertion. Freeze validation is now
scalar-only and emits one bounded marker after alignment. Live validation is
pending the next continuation cycle.

The next source-matched retry crossed that marker after all 573 surfaces, then
was killed before HIR at 6,359,240 KiB anonymous RSS. The first post-marker
operation passed the complete `ModuleSurfacesByName` struct by value through
freeze resolution helpers. Those helpers now receive only the authoritative
surface/name/index arrays, eliminating the aggregate copy boundary. Live
validation remains pending.

The source-matched retry with scalar helper arguments again completed all 573
surfaces and emitted the alignment marker, but the kernel killed Stage3 at
6,337,076 KiB anonymous RSS before HIR. This falsifies aggregate argument copy
as the dominant retained owner. The three-cycle live retry cap is exhausted;
Stage4, deploy, exact-binary smoke, verification PASS, and main push remain
blocked. The next session must measure or remove the retained compact-surface
payload before freeze rather than repeat this command unchanged.

## Reset-time retained owner attribution — 2026-08-12

An env-gated Stage3 probe sampled 38 representative physical sources at every
`module_surface_build` declaration group. Total sampled persistent deltas were
122,826 objects for route extraction, 22,467 for callables, 16,400 for impls,
3,230 for composites, and under 1,500 for all other groups combined. These are
orders of magnitude below the 7,654,371-object freeze baseline. The dominant
growth occurs after surface construction in `driver_end_transient_parse_scope`:
`ast_reset()` ran only after the discard scope was paused, making its replacement
AST arrays and sentinels persistent on every source. Parser globals are now
cleared while the discard scope is active, before pause; only the materialized
surface is built persistently afterward. The focused streaming ownership
contract passes 12/12 under the diagnostic seed. Live source-matched validation
is deferred because the continuation's three full-cycle cap is exhausted.

The next live retry reproduced the same 7,654,091-object freeze baseline and
6,350,844 KiB anonymous RSS, falsifying reset ordering as the dominant owner;
that semantic change was reverted. Sampled route-to-release pairs prove scope
reclaim is active (48k–283k objects removed per sampled source). The existing
per-file start marker now includes `heap_registry`, so `released - start`
provides a complete retained-surface delta ledger on the next bounded run.

The complete ledger measured 6,847,328 retained objects across 573 physical
surfaces (11,950/file average), accounting for the full growth to freeze.
The largest owner was the 31 KiB export facade `core/__init__.spl` at 116,343
objects; it contains 443 authored export lines. Export route tokenization is now
performed before the discard scope is paused. Persistent surface construction
copies only the final source/local tokens, so full-source line arrays and
split/trim scratch are reclaimed at scope end while authored-source authority
continues to bypass corrupt flat export slots. Live validation is pending the
next continuation because all three bounded cycles were consumed.

## Rebased Stage2 diagnostic-call crash — 2026-08-13

The feature bookmark was rebased onto GitHub `main` at `e67f4f53c7d8`. A clean,
one-worker full-bootstrap rebuilt the stale Rust authority and produced a fresh
25 MiB Stage2 compiler under strict no-stub policy. Stage2 stayed below 400 MiB
RSS; the Rust authority rebuild peaked at 3,545,048 KiB.

The fresh Stage2 then crashed on the second physical Stage3 surface. Its durable
log printed `heap_registry=<invalid-heap:...>` immediately before the SIGSEGV.
Rebase conflict review showed upstream had removed this always-on diagnostic
call, while the memory lane retained it. Start/release progress markers are now
scalar-only; heap-registry calls remain restricted to opt-in memory probes. The
focused streaming ownership contract passes 15/15. Final live bootstrap
validation remains required; no main promotion or deployment claim is made.

The final bounded cycle rebuilt Stage2 from the current source in 91 seconds,
then reproduced SIGSEGV on `driver.spl`, the second physical Stage3 surface.
Markers were scalar-only and max RSS was 326,520 KiB, so both heap-registry
interpolation and memory exhaustion are falsified as this crash's cause. The
three-cycle session cap is exhausted. The next continuation must debug the
second-surface lifetime/ABI boundary using the retained admitted Stage2 and
cache; it must not repeat the unchanged full bootstrap. Stage3, Stage4,
deployment, essential-tool smoke, and main promotion remain **FAIL**.

## Persistent parser-control ownership — 2026-08-13

GDB localized the rebased second-surface SIGSEGV first to
`ast_gen_harden_enabled()` and then, after scalarizing that cache, to
`ast_decl_prefer_arena()`. Both were module-global control arrays first
initialized inside the discard parser arena and dereferenced after its mapping
was released. The shared fix seeds `ast_reset()` before opening each discard
scope, making all parser control slots persistent while leaving per-source AST
payloads discard-owned. The harden enable cache is scalar as an additional
ownership invariant. The focused streaming contract remains 15/15 PASS.

That fix advanced Stage3 from two surfaces to 68 surfaces. It exposed a short
multi-line boolean in `typed_storage_view_producer.spl` that the Stage2 parser
correctly rejected; parenthesizing both compound conditions passes the focused
producer spec 5/5. The final bounded run then parsed and released all 603
physical surfaces, reached freeze alignment with `heap_registry=2,204,251`,
and stayed within 471,164 KiB max RSS. This replaces the former 6+ GiB OOM and
proves small-memory surface parsing now converges.

The process SIGSEGV'd immediately after the freeze alignment marker, before the
next freeze-surface marker. The three-cycle cap is exhausted. The next session
must inspect the generation/view construction boundary after alignment using
the retained admitted Stage2; it must not repeat an unchanged bootstrap.
Stage3 artifact publication, Stage4, deployment, and main promotion remain
**FAIL**.
