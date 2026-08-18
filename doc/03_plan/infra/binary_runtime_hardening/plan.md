# Plan — binary_runtime_pure_simple_hardening

Status: planned, 2026-08-18.
Research: `doc/01_research/infra/sspec_binary/binary_sspec_rt_hardening_frozen_design_2026-08-18.md`
Design: `doc/05_design/infra/sspec/binary_reference_stacked_design.md`

One parent initiative covering the user's 7 goals:

| Goal | Deliverable | Wave |
|---|---|---|
| 1. Remove direct `rt_*` (pure Simple or sanctioned alias), warning→error, critical-check with measured counts | `check-no-direct-rt.shs` + baseline ratchet + alias registry | 1, 3 |
| 2. "Simple can do what C can do" — classify project C, file bugs | `c_migration_inventory.sdn` + bug import | 1, 4 |
| 3. Simple ≥ C perf; C HAL shared with rust/simple/pure-simple, differential + perf compare, then replace | HAL contract + differential framework + perf gates | 4, 5 |
| 4. SSpec binary/protocol/cipher/compress infra with bit tables (stacked words default) | comparator + renderers + adapters | 2 |
| 5. Migrate all rt_ callers; revive rt_ check logic; fix-it diagnostics showing alias replacement | migration by subsystem + W-RT-DIRECT diagnostic | 3 |
| 6. Migrate all project C to Simple with I/O + perf evidence; dual C/Simple runtime robustness framework; update spipe skill + LLM wiki | per-migration 10-step process (research §14/§17) | 4, 6 |
| 7. Find and merge duplications | duplication audit → 4 canonical owners | 1, 6 |

## Canonical registries (single authority; Markdown backlogs are projections)

```
binary_reference_layouts.sdn
runtime_boundary_inventory.sdn
c_migration_inventory.sdn
cross_language_perf_results.sdn
binary_test_coverage.sdn
```

## Waves (detail: research §17)

- **Wave 0 — freeze contracts.** One owner edits SpecReferenceSchema / StackedWordLayout / BinaryEvidence / BinaryDiff / HAL schema / classifications / perf schema. Outputs the schema SDNs above plus `doc/04_architecture/sspec_binary_reference.md`, `doc/05_design/sspec_stacked_layout.md`. No migration starts before freeze.
- **Wave 1 — read-only audits (parallel):** A rt_*/alias archaeology (why the old alias was deleted → `alias_removal_receipt.sdn`, cross-engine parity), B C inventory (import existing C-runtime audit), C SSpec duplication map, D perf infra, E protocol/crypto/compression corpora, F SPipe skill + LLM wiki freshness.
- **Wave 2 — core SSpec:** layout extraction, comparator, stacked renderer, manual renderer, machine evidence, domain adapters. Golden fixtures; no second comparator.
- **Wave 3 — rt_* gate:** alias registry + zero-cost proof (interpreter/JIT/AOT/native/bootstrap/dynload all resolve same target, proven by RUNNING, not compiling); `check-no-direct-rt.shs` fail-closed with structured counts (`direct_total = allowed_provider + generated_boundary + test_oracle + forbidden_product + unclassified`; final: forbidden_product = unclassified = suppressions = 0, scanned_files > 0); baseline ratchet; migration by non-overlapping subsystem.
- **Wave 4 — C→Simple migrations:** per unit: freeze C behavior → SSpec I/O evidence → independent oracle (RFC/NIST/Chromium URL corpus where semantics match) → pure Simple → C/Rust/Simple/PureSimple differential matrix → perf benchmark → flip provider → C becomes test oracle → delete/classify. Destructive HW ops use trace+replay, not 4× execution; shadow mode during migration.
- **Wave 5 — perf closure:** only red/inconclusive benchmark IDs; root-cause taxonomy (research §16); verdict bands: Equivalent ≤1.02 noise bound, Fail >2%, Critical >5% or silent interpreter fallback. Prefer compiler/runtime fixes over call-site hacks.
- **Wave 6 — docs/duplication closure:** delete merged helpers, refresh spipe skill / verify skill / LLM wiki, release gates (research §18 — every critical checker emits counts, never a bare PASS).

## Warning→error phases for direct rt_*

A: critical builds error now; normal builds warn; new occurrences beyond baseline fail CI.
B: baseline only ratchets down. C: zero product callers → error everywhere. D: delete compat handling.

Diagnostic must show the fix: the `std.*` semantic API and the provider-only alias alternative, plus tracking ID.

## Conflict rules (parallel agents)

One owner per interface/registry; separate worktrees; schema versions on every interface change; every receipt records fresh binary hash; no green with zero examples/files scanned; no oracle weakening; failed results stay visible.

## Implementation order

Research §19 (19 steps, schemas first, gate promotion last).

## C-migration test standard (user directive, 2026-08-18)

Every C-to-Simple migration MUST, before the C is retired:
1. **Perf-profile FIRST and fix perf problems before/with the migration** —
   measure both sides on the shared corpus, record the ratio in the registry
   entry; a >2x gap is a PERF finding to fix or file, never to hide
   (crc32's 14.4x->2.25x chain is the worked example).
2. **~100 branch-covering differential cases with SHARED test logic** — one
   deterministic generator loop feeds the SAME inputs to BOTH the C oracle
   and the Simple implementation and asserts equality inside that loop; the
   loop is the shared logic (no duplicated per-side vector lists). Cover:
   length 0..N, byte classes (0/127/128/255), domain boundary values,
   invalid/reserved encodings, UTF-8 multibyte.
3. Published KATs stay alongside the bulk loop.

## Fix test standard (user directive, 2026-08-18)

Every FIX (compiler, runtime, library, script) must land with:
1. **A reproduce test** — a spec that fails on the pre-fix code and passes on
   the fixed code, encoding the exact reported shape (same input, same call
   pattern). A fix whose only evidence is "the old symptom went away" is
   incomplete.
2. **Similar-case tests** — the neighboring shapes the same defect class
   could hit (e.g. a fix for `to_hex` bounds also tests `from_hex` bounds;
   an import-resolution fix also tests the aliased and qualified forms).
   Derive them from the defect class, not just the one reported instance.
3. Both live at the mirror `test/` path of the fixed file and are cited in
   the bug doc's resolution note.
