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

## Gates (measured, fail-closed)

| gate | what it proves | verdict measured 2026-08-18 |
|---|---|---|
| `scripts/check/check-no-direct-rt.shs` | direct `rt_*` ratchet, structured counts; wired into `pre-push-conflict-tree-guard.shs:837` | `PASS — 14800 file(s) scanned, forbidden=12794` |
| `scripts/check/check-binary-sspec-evidence.shs` | binary-evidence suites run, are non-vacuous, and contain negative cases (reserved-violation + corruption render) | `PASS — 6 spec(s) checked, 54 example(s) total, 0 vacuous, negative cases present` |
| `scripts/check/check-dual-run-shadow.shs` | goal 6 dual-run shadow harness (`test/01_unit/lib/common/spec/dual_run_shadow_spec.spl`) runs, is non-vacuous, 0 divergent | `PASS — 13 pair(s) checked, 15 case(s), 0 divergent` (2026-08-18) |

Both have fatal `--selftest` fixtures and print measured counts — never a bare PASS.
The evidence floor ratchets up (37 → 46 → 54 on 2026-08-18) as adversarial cases land.

## Delegating mechanical rt_ migration to a small model

Guided haiku handles call-site rewriting well (5 batches, ~40 sites, correct
provider/comment/quoted-string skips — it correctly refused to rewrite
`"rt_process_run(cmd, args)"` inside an FFI *generator*). Two guide gaps cost
real time, so state both explicitly in any such prompt:
- **Import alias syntax is `use m.{name as alias}`, never `{name: alias}`.**
  Haiku correctly recognised a name collision and reached for an alias, but
  guessed `:`, which is a parse error that blocks every spec in the tree.
- **Rewrite call sites only.** Deleting a local `fn foo(): rt_foo()` wrapper
  and importing `foo` instead is a public-API change: other modules
  `use this.module.{foo}`, and that is the shape of
  `import_triggered_cross_module_symbol_misdispatch_2026-08-18.md`.

## Wrapper migrations must update the std shim (2026-08-18)

`src/lib/io_runtime.spl` is a SHIM: it re-exports an EXPLICIT, hand-listed set
of names from `nogc_sync_mut.io_runtime` (comment in the file: the binary can't
search `lib/*/` subdirs in interpreter mode). `src/std` is a symlink to `lib`,
so ordinary product code's `use std.io_runtime.{foo}` resolves through that
list — NOT through the implementation module.

Adding a wrapper to `nogc_sync_mut/io_runtime.spl` alone therefore migrates
call sites onto a name that resolves to NOTHING. This happened on 2026-08-18
for five wrappers (`hash_text`, `file_rename`, `time_now_monotonic_ms`,
`shell_exec`, `process_run_timeout`) and neither gate caught it:

- `check-no-direct-rt.shs` counts `rt_*` CALL SITES — they really did go away,
  so it reported progress.
- The wrapper spec imports `nogc_sync_mut.io_runtime` DIRECTLY, bypassing the
  shim, so it passed 10/10.

It surfaced only as `[use-warning] 'hash_text' is named in
`use std.io_runtime.{...}` but module '.../src/std/io_runtime.spl' does not
provide it` inside an unrelated guard's output.

**Rule: every new io_runtime wrapper is added in TWO places** — the
implementation module and the shim's export list — and the sanity spec should
import through `std.io_runtime` (the path product code uses), not the
implementation module.

## Measuring perf: two corrections learned the hard way (2026-08-18)

1. **`SIMPLE_JIT_STRICT=1` does NOT select an engine.** Bare `bin/simple run`
   already Cranelift-JITs; the flag only makes codegen failures refuse instead
   of silently falling back. The engine knob is
   `SIMPLE_EXECUTION_MODE=interpreter|jit` (`.claude/rules/testing.md`).
   Measured proof: identical numbers with and without the strict flag.
   `bin/simple test` is the interpreter lane.
2. **Ratios are only comparable within one corpus.** The same `sqrt_f64` reads
   12.2x on the spec's corpus and 61.8x on a 1e-300..1e300 corpus, because
   range reduction iterates far more at extreme magnitudes. Always state the
   corpus alongside the ratio, and never compare a before/after measured on
   different corpora (the base64 44.7x->35x claim was withdrawn for exactly
   this reason; its pinned-corpus A/B gave the real figure, 438x->32x).

Corollary for harnesses: bind call results to locals before comparing —
`if not _approx(f(x), g(x), tol):` with nested call arguments produced a wrong
boolean under `SIMPLE_EXECUTION_MODE=jit`.

### `result = result + x` O(n^2) accumulation: canonical remedy currently BLOCKED (2026-08-18)

`common.string_builder.StringBuilder` (`src/lib/common/string_builder.spl`,
array-of-parts + single `join`) is the existing intended canonical fix for the
`result = result + x` scalar accumulation pattern flagged by C-MIG-0023/0035
and the base64 migration. **It is not currently safe to adopt library-wide**:
measured on `to_upper_ascii` (naive `+` vs `StringBuilder`, synthetic corpus,
n=100..30000):

- **JIT lane** (`bin/simple run`): `StringBuilder` wins, crossover ~n=100-300,
  up to 11.6x faster at n=30000 (54ms vs 627ms) — behaves as designed.
- **Interpreter lane** (`SIMPLE_EXECUTION_MODE=interpreter`, also what
  `bin/simple test` runs under): `StringBuilder` LOSES at every measured size
  and gets relatively worse as n grows — 1.7x slower at n=100, 34.4x slower at
  n=30000 (10.8s vs 314ms) — i.e. worse-than-quadratic in this lane. Full
  numbers and analysis:
  `doc/08_tracking/bug/string_builder_interpreter_push_worse_than_quadratic_2026-08-18.md`.

**Root cause LOCALIZED 2026-08-18, not yet fixed.** Confirmed with an
independent minimal repro (`self.items.push(x)` on a plain class field, no
`StringBuilder`/text involved: 30x growth in n -> ~58x growth in interpreter
wall time; flat under JIT). Two compounding causes, both required for a real
fix: (1) `handle_array_methods`'s generic `"push"|"append"` arm
(`interpreter_method/collections.rs:179-184`) clones the entire backing `Vec`
on every push when the receiver is not a bare local identifier — which is
exactly `self.field.push(x)`, i.e. how `StringBuilder` accumulates; (2) a
deliberate, pre-existing ownership-sharing choice in the identifier-receiver
method-dispatch fast path (`interpreter_helpers/patterns.rs:578-606`, "zero-
copy self" — re-inserts an `Arc::clone` of the callee's `fields` map into the
caller's env for the WHOLE call, not just argument evaluation) pins that
field's Arc refcount at 2 for the entire method body, defeating ANY local
`Arc::make_mut` fix at the push call site alone. An attempted fix for (1) was
built, compiled clean, and benchmarked against a locally-built seed
(`CARGO_TARGET_DIR` under `/mnt/data`, deployed `bin/simple` untouched) — it
made the harness SLOWER (11.25s vs 4.66s at n=30000, not the deployed-binary
StringBuilder numbers above), proving (2) must be fixed too, and was reverted.
Patch sketch for the combined fix is recorded in the bug doc.

**Verdict: StringBuilder does NOT become blanket-adoptable once "this fix" is
deployed, because there is no single fix yet — the real fix is two coupled
changes (see bug doc), still unimplemented.** Because most of this codebase's
tests and tooling run under the interpreter lane, `StringBuilder` cannot yet
be recommended as a blanket remedy for this pattern — a commit adopting it at
two call sites (`to_upper_ascii`, `svmg/assembler.disasm`, `22faace491c`) was
reverted for exactly this reason. Use it only where the caller is known to run
under JIT/codegen; otherwise leave the `result = result + x` pattern in place
(correct, just not optimal) until BOTH interpreter-side causes above are
fixed, and re-measure (harness in the bug doc) before re-adopting.

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
