# Static guard and build-pruning implementation work packages

Status: ready for root review and scoped implementation assignment; no production source edited by this design task. [Detail contracts](../../05_design/static_when_tldr_build_pruning.md) precede parallel edits. Full acceptance remains [REQ-001 through REQ-015](../../02_requirements/feature/static_when_tldr_build_pruning.md).

## Ownership and sequencing

Primary architecture reviewer: Astra lane. Merge/integration owner and final normal/highest-capability reviewer: root. Next implementation owner: whole_execution lane, pending root dispatch to an isolated owned sparse candidate. Support_policy owns independent measurement/harness evidence. Lower-model sidecars: N/A for semantic implementation; no unreviewed generated code/manual admission. No source edits in live/bootstrap or another lane's frozen overlay.

| Package | Disjoint owner files / integration boundary | Dependency and completion evidence |
|---|---|---|
| A: typed registry/config | New common/static_condition/static_domain_v1.spl; unit spec static_domain_v1_spec.spl | Exact API below/detail frozen; real typed IDs, no host I/O; invalid/ambiguous/dynamic/seal/oneof controls |
| B: guard algebra | New common/static_condition/static_guard_v1.spl; static_guard_v1_spec.spl | A; bounded builder, local simplification, canonical codec, randomized/property truth tables |
| C: structural scanner | New frontend/static_condition/static_region_scan_v1.spl; static_region_scan_v1_spec.spl | A/B; lexical-owner review; inactive syntax/branch/span tests |
| D: first work avoidance | New driver/static_condition/static_closure_v1.spl plus scoped driver_source_loading.spl and driver_source_pipeline_loading.spl integration | C; explicit Result/config propagation and real zero-probe false import fixture; pure-Simple native executable |
| E: Boolable migration | New 30.types/static_condition_boolable_v1.spl plus existing truthiness/typecheck/interpreter/backend owners, exact edit list after call-path audit | A/B; compiler owner review, mode-versioned compatibility and native/interpreter parity |
| F: guarded summary/AST | New common/cache_contract/guarded_dependency_summary_v1.spl and frontend/cache_artifact/guarded_tldr_projector_v1.spl; canonical codec/registry/GC pin integration | B/C/E; semantic reference/readset producer and actual parser->AST producer; schema migration, cross-host bytes |
| G: semantic closure/cache | Driver static_closure and canonical cooperative client integration; effect/link readset owner | D/F; source/config/aspect/capture invalidation, SCC, standalone/runner parity, complete closure proofs |
| H: acceleration | SIMD/GPU frontend adapter files chosen only after real provider audit | C/F; scalar reference, bounded transfer, capability fallback, end-to-end dispatch measurement |
| I: documentation/migration | Syntax/module/platform/build guides, SPipe agent policy, generated spec manuals, lint owner | E/F/G; deterministic fix spans, no new cfg, best-model manual review |

Proposed paths are relative to src/compiler except test files, whose exact locations are in the test matrix. Do not edit a shared owner from two packages concurrently. A/B/C may use independent files; root integrates D/F/G sequentially at shared boundaries.

## Next bounded slice: A only

Implement A first as a genuinely small, independently verifiable artifact. Freeze universe-bound `StaticAtomV1(universe_digest, domain_id, member_id)`, `StaticUniverseV1`, `StaticConfigV1`, `StaticDomainCardinalityV1` and the five exact functions in the detail design. Preserve builtin IDs in a checked table; explicit one-of/set metadata; aliases normalize once. Full sealed extension data is validated, including stable provider IDs, ambiguity and dynamic rejection. No arbitrary provider execution and no host platform reads.

Owned candidate files:

- `src/compiler/00.common/static_condition/static_domain_v1.spl`
- `test/01_unit/compiler/static_condition/static_domain_v1_spec.spl`
- matching generated/manual `doc/06_spec/01_unit/compiler/static_condition/static_domain_v1_spec.md`

Required initial cases: one-of valid selection; conflicting/missing one-of rejection; set multi/empty selection; unknown/wrong-domain error; ambiguous alias; dynamic member rejection; stable builtins under reorder; canonical universe/config digest under reorder; changed seal rejection; cross-universe atoms with reused numeric IDs and empty seals rejected during config construction/evaluation; compact wire container stores seal once and restores atom provenance on decode; same universe with two targets gives different membership without host environment access. Assertions compare actual APIs and encoded identities, not a mirrored test implementation.

A changes no language behavior and cannot claim build speedup. Its admission enables B/C; the first measurable build optimization is D. Do not call A the full feature. Any actual compiler defect encountered should be fixed in its owner or recorded concretely, not worked around by unsafe syntax/truthiness assumptions.

## First measurable vertical slice: A+B+C+D

Fixture: an entry imports an available shared dependency and contains a false OS branch naming a deliberately nonexistent module. The instrumented resolver must observe zero probes/reads/parses/submissions for that false module. A matching target must activate the edge and fail with a real missing-module diagnostic. Nested elif/else selects exactly one branch; malformed or typo guards fail before imports. Preserve source spans and current active import behavior.

Both standalone compiler and runner invoke the same scan/config boundary. Record source bytes, candidate probes, module parse/HIR/MIR counts, queue submissions, wall/CPU/tree RSS. Compare an unconditioned control and broad reference closure; no unsafe old fail-false condition path counts as reference truth. Existing target/source cache partition tests must change selected config in the same process and observe re-evaluation.

## Verification and profile discipline

Use the pure-Simple native runtime by default. Seed diagnostics require explicit root authorization and are recorded separately; unsupported no-follow I/O externs cannot be replaced by weaker simulated operations. Existing runner8 unit successes are unrelated to native filesystem qualification. Prior cooperative initial30/import retries remain separate evidence and must not be rerun for this feature.

Before a run, pin source/producer/options/fixture, exact counts, negative assertion control, runtime capabilities, collector and resource budget. Include process-tree closure and bounded output. Use at most three verify/fix cycles per slice and never repeat green acceptance checks without changed inputs or an unresolved concern. No broad successor or live source mutation enters a frozen packet.

Perf suite: tiny standalone SPL, same payload through real native runner, no-condition large module, many false platform imports, multi-target common source, required initializer/coherence/aspect fixture, cold/warm/private-body/public-signature/guard/config/capture edits, and contended shared dependency. A script stalled before compiler launch is setup evidence only. Report native 10x4 separately and only after actual independent compiler-context migration/qualification; process count is not thread proof.

Root reviews exact code, source/docs/tests matrix and resulting receipts before enabling any production path. Final verification includes required compiler/lib/MCP checks when executable source changes and the appropriate bootstrap/native smokes; this documentation-only design does not fabricate those results. Release follows verified merged work, never design completion alone.