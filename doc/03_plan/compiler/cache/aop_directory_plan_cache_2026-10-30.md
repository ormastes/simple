# Directory AOP plans: existing-owner cache and publication requirements

Base da5d2bd4e23f1a30bcde314b85f053e2cc4d639e. Astra design/final review; Luna implementation/tests. Executable evidence UNRUN; no compiler launch. This document separates the bounded actual hot-path change from required directory publication and inline-body work.

## Existing owners and first implementation

`00.common/cache_contract/aspect_match_shard_v1.spl` already owns PointcutSelectorV1: a flat PointcutSelNodeV1 array with left/right indices and root. It is already a binary traversal representation; introduce no second bytecode or wire schema. PointcutMatchCacheV1 stores scoped results keyed by selector identity and directory facts. Facts bind directory scope, membership, join-point paths/attributes, child roots, negative membership and active guards. Preserve these keys; identical selectors do not make directory match results interchangeable.

`80.driver/cache/aop_match_cache_driver_v1.spl` owns AopMatchDriverStateV1 and the actual aop_match_shard_acquire_v1 path. It currently reparses selector text before every result-cache lookup. Implement parsed-plan caching in this same owner, not a new service or registry.

Frozen API:

- Existing AopMatchDriverStateV1.create() selects capacity 256.
- Add static create_with_selector_capacity(capacity:i64) -> Result<AopMatchDriverStateV1,text>; nonpositive capacity returns `selector-plan-capacity-invalid`.
- Add aop_selector_plan_acquire_v1(state, source:text) -> PointcutSelectorV1 and call it from the actual shard acquire instead of reparsing.
- State fields: selector_plans (exact source alias -> immutable PointcutSelectorV1), selector_plan_keys (FIFO), selector_plan_capacity, selector_parse_count, selector_plan_hits, selector_plan_evictions.

Exact-source lookup key is `aop-selector-runtime/v1` plus a NUL and source. A hit directly returns the stored value and increments hits: no parser, index rebuild, whole-cache scan, recency reconstruction or DB access. A miss invokes the existing parser once and increments parse count. Within the bounded resident plans, reuse a canonical plan when selector_digest, supported, form, operand and needs_universe agree. For a reused semantic plan, source is the first representative spelling; this new helper does not promise the latest spelling. The existing selector digest domain fixes parser semantics/schema; the runtime prefix fixes cache layout. Parsing itself does not read host/target configuration. Directory match facts retain all relevant configuration dependence.

At capacity, evict the oldest exact-source alias on a miss, rebuilding the bounded dictionary rather than relying on the known native Dict.remove return contract. Preserve other aliases and do not mutate any stored plan or returned old value. Both alias count and resident references are bounded by capacity. This is FIFO, not LRU. Semantic interning/eviction work is on misses only. A process-local state does not persist across compiler-provider changes.

This cache reuses the existing immutable value/node-array surface; source code can prove no explicit rebuild and semantic preservation, but physical pointer sharing/allocation freedom still requires native measurement. There is no new raw-pointer pin API. Owner-local synchronous selector parsing is cheap bounded work and does not require an AsyncRef for every attribute. This slice does not claim multicore publication or a full inherited-directory traversal cache.

## Author-first acceptance

Luna owns a new unit file under test/01_unit/compiler/driver, written before production changes. Cases: exact hit parses once; semantically equivalent spelling shares canonical digest/value; changed selector creates a different plan; capacity-one eviction keeps a previously returned plan semantically intact; zero capacity rejects; actual aop_match_shard_acquire uses the cache and does not reparse when a new member or guard changes only directory match results. Use an independently computed existing matcher oracle for retained-plan behavior, not only counters. Unsupported selectors preserve existing conservative fallback.

Production ownership: only aop_match_cache_driver_v1.spl changes in this slice. Existing aspect_match_shard_v1.spl wire/result semantics, TLDR, RR, mono and publication owners are untouched. Astra owns this design and final review. The acceptance suite may reference these tests but must not credit them as full directory-update completion.

## Directory generation requirement (not implemented by first slice)

Before compiling source, that directory's admitted __init__.tld must contain validated effective aspect/pointcut context. PackageInitTldV1 already contains parent_scope_digest, membership_root_digest and aspect_root_digest; use its existing owner and physical binding, not a parallel directory manifest.

An aspect update captures the complete old/new affected directory union, including inherited scope, previously negative matches, added/removed/renamed members and newly created directories. Recompute each affected directory's effective aspect context against exact frozen membership/configuration. Publish the aspect TLDR only after all required directory results are admitted, with an exact generation/root completion receipt. A timestamp is not completion proof. A new directory must evaluate applicable ancestor/local aspects and produce its __init__.tld before its source compile is admitted. Unrelated directories do not wait behind a global phase barrier.

Bind this to the existing CacheNamespaceAuthorityV3/ScopeV3 expected-head/reader-pin authority: begin, sync_object, commit_selected, finish/abort. Current native/Rust providers are Unsupported and the live three_payload_generation_publisher gate is closed. No durable publication or before-source barrier is qualified by this design. Do not bypass through raw rename or invent another journal/writer.

## Required directory traversal cache and typed attachments

A future combined directory traversal index is a derived cache attachment, separate from immutable TLDR semantic bytes. Its key must bind owner TLDR semantic facet, attachment kind/schema, compiler/provider identity, relevant configuration and dependency/effective-parent-plan identities. Reuse the existing action/attribute/index owner after its concrete admission seam is established; no second cache service. Build once per admitted exact key, using an existing shared AsyncRef request only when production is expensive or can suspend. Bound residency, retain old readers, and create a new immutable version on context change rather than mutate a published index.

Compiled aspect pointcuts and inline functions are distinct typed attachment kinds. Unchanged ancestor selectors reuse admitted immutable selector plans, while child-local delta/index and effective ancestor context remain directory-scoped. Match results never reuse blindly across membership, guards, path resolution or prior negatives. Inline-body attachment keys must bind the body semantic facet and dependencies: stable interface identity does not permit reuse after a body edit. Interface-only demand must not load an inline body. Existing HIR/MIR body/archive owners must be audited before exposing an inline attachment API; this slice introduces none.

Ready attachment reads must avoid rebuild/redecode, payload copying and mandatory DB transactions. Persistent representation is allowed only through an existing admitted owner/schema; runtime caches and refs do not become TLDR semantic bytes. Tests for the later directory work must include unchanged parent-plan identity reuse, child override, ancestor change across old/new directories, negative-to-positive new membership, protected old readers, and exact generation-last publication. These gates remain open beyond the parsed-selector cache delivered here.

Scoped inline-owner audit: `60.mir_opt/mir_opt/inline.spl` already exports FunctionInliner/ModuleInliner and inline_run_on_function/module from its split owners. `80.driver/cache/reader/template_body_loader_v1.spl` owns content-bound template body decisions; its comment explicitly says the driver loads admitted owner HIR and the decision table is not a body loader. `50.mir/hir_expression_artifact_v1.spl` owns authority/archive/body/expression-digest records and transient decode, but supports declaration expressions (defaults/initializers/discriminants), not arbitrary inline function-body attachments. Reuse these owners where applicable; none proves an existing generic TLDR inline-body cache attachment ABI. No inline source change is included here.
