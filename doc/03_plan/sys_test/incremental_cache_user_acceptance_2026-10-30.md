# Incremental cache user acceptance — 2026-10-30

Status: UNRUN; end-to-end acceptance BLOCKED. This is an authored inventory and acceptance contract, not a test report. No compiler, native build, test runner, or SPipe docgen was executed. The qualified Linux full CLI is unavailable and the prior compiler diagnostic retry budget is exhausted. Do not substitute the Rust seed or count static review as execution.

2026-10-31 source update: the matrix below records the original source assessment. PR #5526 implements the FileFiber canonical await bridge and adds 16 authored cases (11 unit, 2 integration, 3 system); its former missing-adapter gap is now **implemented, runtime UNRUN**, with unsafe lifetime/fatal-retention limits retained. PR #5524 transports advisory macro candidates but still requires full recheck where publication/object-generation authority is absent. PR #5518 adds prelink identity coverage, PR #5522 runner-facade coverage, and PR #5520 source-reviewed telemetry with no added executable case count. The existing [SDN inventory](incremental_cache_execution_inventory_2026-10-30.sdn), section `followup_accounting_2026_10_31`, records exact paths and the 3e4df source overlay: **50 paths, 279 authored cases, no feature execution credit**. Older Cranelift runner controls (green 2/red 1) and the C delegated-parent cleanup control are separately scoped evidence; neither qualifies these feature cases or LLVM.


## Evidence rules

A case count means an executable SSpec `it` block, not a step, assertion, source listing, successful compilation, or passed scenario. Supporting component cases do not close an end-to-end requirement. Every future run must identify the exact runner artifact/digest, host/provider, source revision, scenario, input/output artifact digests, expected comparator, and actual result. Native HAL evidence must name the admitted native provider; Unsupported/Unavailable is a rejected capability, not successful execution. Stage traces are opt-in diagnostics and cannot establish custody or artifact validity.

For a missing production API, keep the desired case BLOCKED. Do not add mock producers, test-only cache decisions, fabricated receipts, source-string assertions, `expect(true)`, or skip-based passes. Existing failure/unsupported cases verify rejection only. Runtime cached references must never be serialized in evidence as durable pointers.

## Requirement-to-scenario matrix

All rows are UNRUN. PARTIAL denotes authored supporting coverage, not a partial execution pass; GAP denotes a missing full-path production adapter/oracle. The user-selected behavior below is fixed; no requirement option is being selected implicitly.

| ID | Required scenario and exact acceptance oracle | Existing/new supporting subject | Remaining gap |
|---|---|---|---|
| REQ-CACHE-001 | Same-key first TLDR caller claims once; second awaits canonical wake; both observe identical immutable result; unrelated key progresses | Existing lockless-map/AsyncRef specs; active TLDR owner integration | PARTIAL: actual TLDR production caller and scheduler run required |
| REQ-CACHE-002 | Producer failure and cancellation release all applicable waiters with one terminal result; late subscribers observe result immediately | AsyncRef terminal, wake, interest specs | PARTIAL: TLDR failure/cancel route and scheduler delivery |
| REQ-CACHE-003 | 3000 distinct logical keys/requests admitted within declared bounds, bounded worker/thread count, exact terminal totals | Lockless-map boundary specs | GAP: 3000-request production run; OS-thread creation is not this oracle |
| REQ-CACHE-004 | Valid OBJ invokes writer only: parse/HIR/MIR/object-generation counts all zero | Existing object reuse/admission specs | GAP: exact full stage counters and immutable artifact witness |
| REQ-CACHE-005 | Valid HIR invokes MIR/object only; valid AST invokes HIR/MIR/object; no cache invokes parse once | Existing frontend packed AST specs | GAP: deepest-valid-stage production adapter and stage counts |
| REQ-CACHE-006 | Resident stage reuse performs no save/reload; missing stage falls back only to nearest valid predecessor | Existing packed AST hit-path specs | GAP: cross-stage resident and IO counters |
| REQ-CACHE-007 | OBJ logical backref resolves HIR then AST lazily; dropping resident data preserves immutable IDs and valid lookup | Packed AST supporting specs | GAP: complete immutable OBJ/HIR/AST chain and lazy loader |
| REQ-CACHE-008 | Same HIR retains all host/target conditional alternatives; two explicit MIR configs select different arms | HIR target-key spec only proves target-separated keys | GAP: current cfg-arm dropping cannot claim portable HIR |
| REQ-CACHE-009 | Hot optional fields set once; dense array+bitmap and sparse map selected by frequency; absent, empty, unresolved remain distinct | SPAB xref set-once spec | GAP: general optional attribute owner and storage-policy tests |
| REQ-CACHE-010 | Existing index pointers reject wrong container/version, retain index identity; hash references survive rebucketing by stable entry identity | Packed AST tests and map boundaries | GAP: complete extended pointer contract and rehash/repack oracle |
| REQ-CACHE-011 | Cached runtime container reference pins lifetime, is dropped on load, never persists; repack remaps every AST/HIR index | Packed AST codec tests | GAP: HIR/pointer pin lifecycle and repack integration |
| REQ-CACHE-012 | Verified identical output skips write and preserves timestamp; changed bytes with same name/time fail reuse | Native zero-work admission supporting suite | GAP: writer invocation count and filesystem timestamp witness |
| REQ-CACHE-013 | Filename-only reuse allowed exclusively for verified immutable content-addressed identity; mtime alone never authorizes | Existing cache digest/admission specs | GAP: paired same-mtime changed-content integration |
| REQ-CACHE-014 | SOSIX binary copy publishes atomically, preserves arbitrary bytes, never overwrites existing immutable object | Existing atomic-claim/writer-admission specs | GAP: actual binary copy/publish syscall-owner integration |
| REQ-CACHE-015 | Failed publication leaves old selected artifact intact; post-publication sync uncertainty differs from pre-publication failure | Existing durable writer admission specs | GAP: fault injection at each real publication boundary |
| REQ-CACHE-RR-001 | Macro provider change re-expands exact direct/nested/negative users; interface cutoff excludes unaffected users | Macro manifest/projector and RR owner suites | PARTIAL: compiler re-expansion exact-set oracle |
| REQ-CACHE-RR-002 | Generic RR selects canonical instance+demand-kind+target; type-only demand produces no OBJ; duplicate demand reuses closure | Generic instance/prelink suites; active RR/mono owners | PARTIAL: exact instantiation and artifact closure counts |
| REQ-CACHE-RR-003 | Unique committed forward manifests drive add/remove/count/cleanup; replacement atomic; replay idempotent; failed compile preserves old | RR atomic-generation model/coordinator suites | PARTIAL: durable producer replacement integration |
| REQ-CACHE-RR-004 | Zero scoped count permits scoped cleanup but does not delete pinned/shared artifacts | RR owner suite | GAP: pin/GC owner integration |
| REQ-CACHE-RR-005 | Any SOSIX RR read/write failure yields Unknown over FULL scope; rebuild latest root; restart if root changes | Active RR owner failure scenarios | PARTIAL: durable latest-root race/restart execution |
| REQ-CACHE-RR-006 | Incoming-reference churn does not rewrite unchanged provider TLDR | RR owner/source contract | GAP: exact bytes, write count, timestamp integration |
| REQ-CACHE-AOP-001 | Directory TLD binds inherited parent context, membership and aspect roots; malformed context rejected | NEW directory_tldr_semantic_binding_spec: 4 codec cases | PARTIAL: serialization only |
| REQ-CACHE-AOP-002 | Every SRC compile first validates directory TLD and effective inherited pointcuts | AOP owner design; package-init codec support | GAP: before-SRC gate and ordered runtime event oracle |
| REQ-CACHE-AOP-003 | Aspect update recomputes ALL old/new affected directories including negative/new matches, then publishes aspect TLD last | AOP owner design | GAP: generation-completion proof and fault/race cases; mtime insufficient |
| REQ-CACHE-AOP-004 | New directory evaluates inherited aspects and creates valid directory TLD before first compile | AOP owner design | GAP: directory discovery and before-compile integration |
| REQ-CACHE-AOP-005 | Parent selector plans and binary traversal indexes reuse exact semantic digest/schema; results remain membership/guard/path-sensitive | Active AOP owner selector-plan tests | PARTIAL: execution and negative identity matrix |
| REQ-CACHE-MONO-001 | Removing standalone monomorphization preserves generic calls, instances, target/demand behavior and closure | Active monomorphization owner regression specs | PARTIAL: qualified runtime regression execution |
| REQ-CACHE-RUNNER-001 | BuildRunner/TestRunner report failure when real child fails or output evidence is missing/mismatched; success requires all outputs | Result admission failure specs | PARTIAL: real child native run and exact exit/output digests |
| REQ-CACHE-RUNNER-002 | Recovery capacity is per-host; overflow fails before ownership, unrelated host proceeds, terminal rows consume no slot | Recovery capacity/host boundary specs | PARTIAL: actual host/provider run |
| REQ-CACHE-RUNNER-003 | Native HAL provider and host isolation are admitted explicitly; legacy/fabricated/unsupported receipts reject | Process observation rejection specs | PARTIAL: real admitted HAL execution, not rejection alone |

## Frozen new SSpec contract

Owner: acceptance-suite lane. Production owner: `compiler.common.cache_contract.package_init_tld_v1`. Fixture: `directory_tldr_fixture_v1(parent: text?, membership: text, aspect: text)`. APIs: `package_init_tld_encode_v1`, `package_init_tld_decode_v1`, `package_init_tld_valid_v1`. Step names: “Bind inherited context and directory membership”, “Decode the stored directory contract”, “Reject malformed inherited context”. All other digest fields use real SHA-256 fixture digests.

Four cases preserve fields on roundtrip, distinguish parent-only changes, distinguish independent membership/aspect changes, and reject malformed parent digest. This does not simulate a publisher. Exact source: `test/03_system/compiler/incremental/directory_tldr_semantic_binding_spec.spl`; manual: `doc/06_spec/03_system/compiler/incremental/directory_tldr_semantic_binding_spec.md`.

## Ownership and bounded verification

Primary acceptance owner freezes interfaces and reviews Luna-authored cases. Luna directory-contract lane owns only the new spec/manual; Luna inventory lane is read-only. Existing TLDR, RR, AOP, and monomorphization owners retain their source/test files. Root is merge owner and final runtime reviewer. No passing assertion or generated-manual claim is inferred from this handoff. Once a qualified runtime exists, execute each criterion once; failures require new evidence or implementation changes before retry, within the shared six-cycle cap.

## Exact inherited SSpec inventory

Static inventory at `6a44812d73d6`: the five recent test commits contain **34** `it` cases across 12 files. This count excludes the earlier recovery-capacity suites and all other pre-existing tests. A remembered “43” total is not reproducible for this five-commit subject and must not be used without identifying its additional files. New directory contract adds 4, for **38 authored cases in this explicitly enumerated subject**, zero executed in this lane. This is not a whole-repository total.

| Commit | Exact test file | Cases | Evidence scope |
|---|---|---:|---|
| 6a44812 | test/01_unit/lib/nogc_async_mut/async_ref_interest_contract_spec.spl | 2 | Invalid interest admission preserves reservations |
| 6a44812 | test/02_integration/lib/async/async_ref_interest_contract_spec.spl | 3 | Stale wake, partial cancellation, last-interest retirement |
| 51e1c939 | test/01_unit/lib/common/task_runner/result_admission_failure_contract_spec.spl | 5 | Receipt/output admission and retry bounds |
| 51e1c939 | test/02_integration/app/buildrunner/result_admission_failure_contract_spec.spl | 2 | Adapter preserves failure/incomplete output rejection |
| d921703c | test/01_unit/lib/nogc_async_mut/lockless_map_boundary_contract_spec.spl | 5 | Capacity, collisions, descriptor reuse, signed keys |
| d921703c | test/02_integration/lib/async/lockless_map_boundary_contract_spec.spl | 1 | Exact shared slot before/after publication |
| d15892fd | test/01_unit/lib/common/process_observation_untrusted_receipts_spec.spl | 2 | Untrusted/absent/malformed receipts rejected |
| d15892fd | test/02_integration/lib/sosix/process_observation_rejection_contract_spec.spl | 3 | Unsupported provider/request rejection |
| af03371a5 | test/01_unit/lib/common/task_runner/recovery_host_boundaries_spec.spl | 3 | Per-host capacity and terminal-row exclusion |
| af03371a5 | test/01_unit/lib/nogc_async_mut/async_ref_terminal_contract_spec.spl | 4 | First terminal result wins; invalid starts reject |
| af03371a5 | test/02_integration/app/buildrunner/recovery_host_boundaries_spec.spl | 1 | Saturation isolation across hosts |
| af03371a5 | test/02_integration/lib/async/async_ref_wake_contract_spec.spl | 3 | Idempotent delivery, failure completion, late ready |

Additional existing supporting suites, excluded from the 34-case subject: `test/03_system/compiler/feature/native_zero_work_admission_spec.spl` (9); `test/01_unit/compiler/frontend/packed_ast/spab_xref_set_once_spec.spl` (4); `test/01_unit/compiler/frontend/packed_ast/flat_pool_packed_v1_spec.spl` (9); `test/01_unit/compiler/frontend/packed_ast/flat_pool_packed_real_spec.spl` (3); `test/01_unit/compiler/frontend/packed_ast/spab_hit_path_spec.spl` (4); `test/01_unit/compiler/frontend/packed_ast/spab_sealed_hit_spec.spl` (5); `test/01_unit/compiler/driver/hir_cache_key_target_spec.spl` (4). HIR target-key separation is not target-neutral conditional retention.

AOP plan-owner follow-up: existing `PointcutSelectorV1` already has binary nodes and root. The active owner is adding bounded parsed-plan reuse on `AopMatchDriverStateV1`, with exact-source parse counters and canonical semantic identity; membership/negative/guard/path inputs remain in result-cache validity. Planned tests must show a result miss with selector-plan reuse after a new negative member or guard change. These cases do not close directory generation/publication requirements.
