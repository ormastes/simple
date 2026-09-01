<!-- codex-design -->
# Native module cache invalidation system test plan

## Scope

Executable mutation/prevention coverage for body edits, signature/layout edits,
resolution candidates, unrelated siblings, missing/corrupt witnesses, and
provider/compiler/target/options identity. Full bootstrap, production-driver
execution, and remote caches are excluded. A focused structural scenario covers
the promoted production-driver authority gate.

## Execution

1. Run the existing bounded baseline: `action_key_spec.spl` and
   `persistent_code_cache_invalidation_spec.spl` once each.
2. Run exactly:
   `SIMPLE_LIB=src <admitted-simple> test test/03_system/app/compiler/feature/native_module_cache_invalidation_spec.spl --mode=interpreter`.
3. Generate and review the mirrored manual with `spipe-docgen --no-index`.
4. Authority performance runs evaluate 1,000 actions; they are not part of
   this bounded design lane.

## Bounded baseline receipt (2026-08-29)

- Runtime route: repository `bin/simple`; it warned that the resolved executable
  is the Rust bootstrap seed, so these results are diagnostic rather than
  self-hosted release evidence.
- `action_key_spec.spl`: PASS, 32/32 assertions, 254 ms reported duration.
- `persistent_code_cache_invalidation_spec.spl`: FAIL, 11/18 assertions,
  244 ms. Seven existing sabotage cases fail: five reference missing helper
  `read_entry`; non-numeric-body expected `length-mismatch` but received
  `checksum-mismatch`; foreign-magic expected `bad-magic` but received
  `truncated`.
- New mutation system spec: PASS, 9/9 assertions, 194 ms reported duration.
- `spipe-docgen`: BLOCKED before generation by unresolved `index` in
  `count_test_items`/`extract_scenario_list`, then missing `run_spipe_docgen`.
  The reviewed hand-written mirror remains the manual evidence.
- Repository layout audit found 3,253 pre-existing executable `*_spec.spl`
  files under `doc/06_spec`; this lane added none. The global zero-count release
  gate remains blocked outside this feature scope.

Pass requires every mutation to have a positive-control hit, every unsafe
mutation to change identity or reject authorization, deterministic ordering,
and no placeholder assertions. Missing runtime capability is reported, not
converted to a pass.

## Traceability

| Requirement | Executable scenarios | Evidence |
|---|---|---|
| REQ-001 | unchanged, body, signature, layout, resolution, provider/config | 6 scenarios; system spec + manual |
| REQ-002 | missing/corrupt/legacy and authoritative exact-match gate | rejection cases plus driver scenario; system spec + manual |
| REQ-003 | body parity, unrelated sibling, complete-witness authority | 3 mutation scenarios plus driver scenario; system spec + architecture |
| REQ-004 | canonical order, resolver order/generation, sibling isolation, bounded decision receipt | 4 scenarios; system spec + architecture |
| REQ-005 | stable configuration root, canonical V1, provider/config boundary, legacy rejection | 4 witness scenarios plus driver scenario; system spec + architecture |
| REQ-006 | unchanged plus every admission mutation and fail-closed read | 8 scenarios; system spec + manual |
| REQ-007 | signature, layout, resolution, provider/config mutations | 4 scenarios; system spec + manual |
| REQ-008 | missing, corrupt, mismatch, legacy non-authority | rejection checks plus driver scenario; system spec + manual |
| NFR-001, NFR-004, NFR-006, NFR-007 | mutation matrix | system spec |
| NFR-002, NFR-003, NFR-005, NFR-008 | authority counters and thresholds | plan; measured at implementation gate |

Manual policy: primary mutation flows are visible; canonical ordering and
corruption details are folded. Evidence kind is `exec`; no UI capture applies.

## Current bootstrap verification ledger — 2026-08-29

| Gate | Current evidence | Required next evidence |
|---|---|---|
| Phase1 matrix | SHA `8999d4e...`; `FAIL`, 11 terminal rows; compiler tests and MCP build timed out at 1,800s; LSP failed at 1,408s | Retain as defect evidence; do not promote |
| Cache reuse | Old LSP frontend/HIR: 0 hits, 22 misses because MCP/LSP roots differed | Next admitted matrix must show shared `tool_builds` reuse without witness mismatch |
| LSP closure | 45 unresolved before narrowing, zero afterward; 126 KiB focused binary | Preserve initialize behavior and broad-facade prevention test |
| MCP closure | 104-symbol diagnostic; handler imports are behavior-bearing and lazy registry cannot load native code | Blocked on versioned late binding; do not delete tools or optionalize required symbols |
| Phase2 MC/DC | Forced standalone SMF failed on interpreter-only constructs | Verify `099b40b5795`: interpreter fallback, recorded `mcdc_skip_reason`, no false coverage claim |
| Phase2 matrix | SHA `5779bd64...`; `FAIL`, 9 terminal rows; LSP build/help passed, MCP build failed | Produce a fresh immutable Phase2 admission |
| Phase3 | Prior evidence predates current source/cache/closure | Rebuild from fresh Phase2 admission, then run build, tests, and tool builds once |

The next receipt must retain elapsed time, timeout/crash class, frontend/HIR
hit/miss counts, cache namespace, compiler hash, and distinct output hashes. A
cache hit cannot turn missing MC/DC evidence or stale lineage into PASS.
