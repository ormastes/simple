# Profile-based switchable container algorithms

**Status:** implementation in progress. [Requirements](../../02_requirements/feature/profile_switchable_container_algorithms.md). [Research](../../01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md).

## Ownership and flow

```text
source container attribute + typed HIR site identity
  -> CollectionPlan extraction and semantic guards
  -> static candidate set and target capability checks
  -> optional admitted .sprof v2 collection metrics
  -> cost/policy selection with recorded explanation
  -> MIR lowering to the selected container operation
  -> per-instance runtime representation and observations
  -> .sprof v2 collection records for a later build/run
```

The compiler owns semantic facts and plan selection. The runtime owns physical storage and measured operations for one instance. The app-level `.sprof` loader owns file I/O, schema and identity admission. Runtime hot operations never read a profile file. Stable AST site and module/target/workload identities prevent stale feedback from crossing builds or targets.

## Implementation state

- `AdaptiveTextSet` and `AdaptiveTextMap` own per-instance linear/hash/ordered storage, explicit runtime algorithm attributes, transitions, and lifetime lookup observations. Their ordered branch uses the AVL tree in `OrderedTextSet`, now with a text value payload for map entries; ordered key comparison paths stay logarithmic through insertion and removal. Allocator and array-growth worst-case bounds still need proof.
- The parsers accept `@collection_algorithm("auto" | "linear" | "hash" | "ordered")` before initialized local `val`/`var` declarations and class/struct fields with defaults. Direct `AdaptiveTextSet`, `AdaptiveTextMap`, `AdaptiveSet`, and `AdaptiveMap` constructor calls route to their respective `attributed_at_site` APIs. An explicit adaptive family annotation also permits a factory initializer; the generated typed static call must validate its result. A conflicting direct-constructor family is a parser error. Generated local sites combine module path, lexical declaration owner, local name, and source-subtree hash; an ordinal distinguishes identical locals within an owner. Field sites include the owner class/struct name. Byte offsets no longer enter site IDs, so unrelated text before an unchanged declaration does not shift its parser-level identity. The whole-source module profile identity still invalidates prior feedback after source edits. Generic `Hash + Eq + Ord` runtime sources now exist, but interpreter/native proof and full supported-type coverage remain open.
- `sprof_collection_profile.spl` currently writes/loads v2 set samples and named P6 metric samples alongside v1 function counters. It validates unique sample identities across both record kinds and can prepare an exact site/target/metric index with count, min, max, mean, p50, p95, and a 64-bin logarithmic histogram. Once built, indexed lookup does no sample scan or sort. `AdaptiveTextSet` observations can emit collection size, lookup count, and current distinct key count; compiler collection/join sites and other runtime containers still need to emit their applicable metrics.
- `collection_plan_selection.spl` now models fail-closed physical choice from typed facts, explicit attribute, P0 readiness, policy, target capabilities, and admitted profile cost. It is advisory and has no MIR lowering connection yet.
- `collection_plan_profile_bridge.spl` supplies the advisory selector with p95 cost facts only for an exact admitted site/target match. A prepared set index computes site/target p95 once. The app-level loader can install an in-memory runtime catalog for direct callers. For `simple run`, the CLI instead installs admitted site/target summaries in the parser before compilation; parser rewrites embed matching prior counts in each attributed initializer via `attributed_with_prior_at_site`. This avoids assuming that the compiler process and a fresh interpreted module share one library-global catalog. The parser catalog is cleared after the run, and cached SMF execution is bypassed while it is active. The two-run integration probe must still execute to prove this path. The compiler optimizer has not adopted the prepared plan path.
- Typed AST site identity with target binding, P6 metric instrumentation and consumption, verified generic set/map implementations, typed CollectionPlan extraction, nested/hash/merge lowering, explanation output, and cross-backend evidence remain required.

## Safety gates

### Identity and toolchain follow-up (2026-09-27)

The current parser hashes only the declaration beneath `@collection_algorithm` for local and field site IDs. The `.sprof` entry-source identity normalizes a valid algorithm argument using lexer token offsets before hashing; it retains path and all other source text. The `source-fnv64-collection-v2` prefix deliberately rejects older full-source profiles. This supersedes the older whole-source invalidation statement above for algorithm-only edits. No admitted runner has executed the new identity cases: installed Windows launchers identify as Rust bootstrap seeds, and the isolated pure-Simple Stage2 test runner does not link against core-C.

### Automatic capture boundary

`simple run` evaluates source through a fresh interpreter module context. The opt-in core-C runtime channel shares bounded size, lookup, and public snapshot events across that boundary, keyed by site and target. `AdaptiveTextSet`, `AdaptiveTextMap`, and `AdaptiveMap` record events; generic `AdaptiveSet` delegates to the map channel. The inactive operation path is one atomic check; the active path uses a process-scoped lock. A snapshot emits one collection sample and four named P6 metric samples per site: peak `collection_size`, `lookup_count`, final `distinct_key_count`, and public `materialization_count`. The 20000-site cap keeps the combined record count within the `.sprof` loader's 100000-sample admission limit. At successful run completion, `simple run --collection-profile-out=PATH --collection-workload=LABEL --collection-target=ID` validates the snapshot and writes the profile in the app layer. Failure aborts capture or fails the command. The earlier three-metric capture block passed an isolated C selfcheck; the four-metric extension awaits current runtime and pure-Simple CLI proof. The process-scoped channel does not isolate simultaneous runs in one process.

`--collection-profile-append` with `--collection-profile-out=PATH` accumulates separate workload runs. The app loader admits both the existing and captured v2 envelopes against the same source module and workload, retains their counter records and collection/metric observations, and serializes fresh unique sample IDs. It rejects malformed or over-limit input before writing. Target identities remain attached to each sample, so later exact-target selection cannot mix them. The new path has source-level regression cases but awaits an admitted pure-Simple runner.

Profile publication uses the shared atomic file-write facade after admission, including the library writer APIs. An invalid append body returns before publication; a failed replacement does not intentionally truncate the existing profile. The CLI regression case seeds a corrupt profile and checks that rejected append leaves its bytes intact.


No compiler-selected index or join plan may land before the research P0 gates: array-map symbol resolution, closure ABI, predicate `any`/`all`, native `Dict` insertion, and cross-backend collection tests. Profile hints only rank candidates whose semantic and target guards have already passed. Critical/adversarial policy excludes an unbounded hash-only worst case and selects a bounded ordered or direct-index representation when its proof applies.
