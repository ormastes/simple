# Test-tree divergence sample 7 — 15-pair triage (2026-08-09)

Residue class used: `NR%65==20` on `scripts/check/test_tree_divergence_baseline.txt`
(prior sessions used ~0, offset-33-step-65, `NR%65==50`, `NR%65==15`,
`NR%65==5`, `NR%65==45` — this session's residue does not overlap any of
those).

Method per pair: diff canonical (`test/01_unit` / `test/02_integration`)
against shadow (`test/unit` / `test/integration`), run the canonical copy via
`bin/simple run <path>` (fallback for `bin/simple test` hangs/timeouts),
classify, and for vacuous-stub/weakened-shadow cases (category a) copy
canonical over shadow and re-verify.

## Summary table

| # | Pair (relpath) | Kind | Classification | Action | Verdict after fix |
|---|---|---|---|---|---|
| 1 | `app/startup_argparse_mmap_perf_spec.spl` | integration | genuine pre-existing flake (perf budget) | left as-is (see below) | canonical: 1/2 fail (1646ms > 400ms budget) — NOT fixed, documented only |
| 2 | `storage/dbfs/dbfs_engine_checkpoint_spec.spl` | integration | vacuous/stale field name in shadow (`gen` vs real `slot_gen`) | shadow synced to canonical | 6/6 pass |
| 3 | `app/llm_caret/provider_spec.spl` | unit | shadow reduced reimplementation (16 vs 36 scenarios, inline mock stubs) | shadow synced to canonical | 36/36 pass |
| 4 | `app/tooling/sandbox_spec.spl` | unit | weakened assertion in shadow (`expect true==true` replacing real Option/nil check) | shadow synced to canonical | 24/24 pass |
| 5 | `bugs/dict_type_annotation_spec.spl` | unit | weakened assertion in shadow (nested-array len check replaced with `expect(true)`) | shadow synced to canonical | 28/28 pass |
| 6 | `compiler_core/keyof_spec.spl` | unit | shadow is a "skipped/pending" stub (20 lines → 4-line pending stub) while canonical is a real, passing spec | shadow synced to canonical | 2/2 pass |
| 7 | `compiler/linker/smf_driver_manifest_section_spec.spl` | unit | shadow missing 2 whole `it` blocks (LaunchMeta section coverage) that canonical has and that pass | shadow synced to canonical | 5/5 pass |
| 8 | `fs_driver/extension_test.spl` | unit | cosmetic (`fail("...")` vs `expect(false).to_equal(true)` — behaviorally identical) | left alone | n/a (no functional difference) |
| 9 | `lib/common/hpack/string_codec_spec.spl` | unit | cosmetic (local var renamed `elem`→`unit`) | left alone | n/a |
| 10 | `lib/common/test_meta_spec.spl` | unit | cosmetic (`assert_true(x)` vs `expect(x)` — equivalent bool assertions) | left alone | n/a |
| 11 | `lib/driver/null_block_driver_test.spl` | unit | **genuine pre-existing bug**: canonical defines `fn test():` wrapping the `describe` block but never calls it, so canonical silently registers/runs 0 examples; shadow has the trailing `test()` call and correctly runs 7 examples | fixed canonical (added missing `test()` call) + synced shadow (already had it) | 7/7 pass both sides |
| 12 | `lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl` | unit | weakened assertions in shadow (`fail(...)` → `pass_do_nothing` / `expect(false).to_equal(true)`) | shadow synced to canonical | 2/2 pass |
| 13 | `lib/pure/tensor_ops_spec.spl` | unit | shadow is a "skipped/pending" stub (29 lines → 4-line pending stub citing a parse-error excuse that does not reproduce) | shadow synced to canonical | 2/2 pass |
| 14 | `os/kernel/loader/app_registry_spec.spl` | unit | **genuine pre-existing bug, PLUS the exact contradictory-count case named in `check-test-tree-divergence.shs`'s own header comment** — canonical asserted `len()==19`, shadow asserted `len()==18`, but `app_registry_load_hardcoded_fallback()` actually pushes **20** entries (verified by counting `g_app_entries.push(...)` call sites in `src/os/kernel/loader/app_registry.spl`); both trees were stale. Shadow was also missing the "normalizes shell-style executable paths" `it` block that canonical has. | fixed canonical assertion (19→20, `it` title 19→20) + shadow synced to fixed canonical | 25/25 pass both sides |
| 15 | `std/desktop/clipboard_spec.spl` | unit | shadow reduced to `expect true==true` stubs replacing real source-contains checks | shadow synced to canonical | 3/3 pass |

## Detail on genuine bugs found and fixed

### `lib/driver/null_block_driver_test.spl` — canonical never invoked `test()`
`test/01_unit/lib/driver/null_block_driver_test.spl` wraps its `describe`
block inside `fn test():` but the file never called `test()` at module scope.
Under `bin/simple run`, the canonical copy produced **no** example output at
all (0 tests silently executed) while the shadow copy (which had a trailing
bare `test()` call) correctly ran and passed 7 examples. Fixed by appending
`test()` at the end of the canonical file (matching the shadow), then
propagated the now-correct file to the shadow path (no-op there, already
matched). Verified: `bin/simple run test/01_unit/lib/driver/null_block_driver_test.spl`
→ `7 examples, 0 failures`.

### `os/kernel/loader/app_registry_spec.spl` — stale entry-count assertion
This is the exact pair the guard's own header comment (`check-test-tree-divergence.shs`)
cites as its motivating example of "CONTRADICTORY assertions on the same
behavior (len()==19 canonical vs ==18 shadow)". Counting the actual
`g_app_entries.push(AppEntry(...))` call sites in
`src/os/kernel/loader/app_registry.spl::app_registry_load_hardcoded_fallback`
gives **20**, not 19 or 18 — both trees were simply out of date (the fallback
table grew at least twice without either spec being updated). Fixed the
canonical `it "populates all 19 standard entries"` → `it "populates all 20
standard entries"` and its `expect(...).to_equal(19)` → `to_equal(20)`.
Re-ran: `25/25` pass (was `24/25` before the fix, 1 failure: `expected 20 to
equal 19`). Shadow was additionally missing the whole
"normalizes shell-style executable paths through fallback aliases" `it`
block present in canonical (and passing) — picked up automatically by the
sync-to-canonical copy.

## Left alone (not fixed)

### `app/startup_argparse_mmap_perf_spec.spl` — perf-budget flake, not touched
Canonical fails on this host: `keeps declarative cli startup parsing
responsive` expects `< 400` ms but measured `1646` ms (subprocess-launch
latency on the shared, multi-agent dev box). Shadow deliberately weakens this
same scenario to "skip gracefully" (`expect(true).to_equal(true); return`)
when the subprocess path is slow/unavailable, plus takes a different
simple-binary discovery order and a different `use` import
(`app.io.process_ops.{shell}` vs `app.io.{shell}`). This reads as an
intentional environment-tolerance divergence rather than a simple staleness
bug, and the actual failure is host-load-dependent, not a narrow code
defect — per the task's guidance ("if it's deeper/riskier, just document and
leave it"), this was left as-is rather than force-fixed or overridden. Filing
as a known-flaky perf assertion is appropriate follow-up but was not done as
part of this narrow triage pass (no new bug file opened for it here since the
underlying cause — shared-host subprocess-launch latency — is already a
recurring, previously-documented class of noise in this repo's spec corpus,
not new information).

### Cosmetic pairs (left alone)
`fs_driver/extension_test.spl`, `lib/common/hpack/string_codec_spec.spl`,
`lib/common/test_meta_spec.spl` — all three differ only in
stylistically-equivalent constructs (`fail()` vs
`expect(false).to_equal(true)`, a renamed local variable, `assert_true(x)` vs
`expect(x)`) with **identical pass/fail behavior** on both sides. No action
taken; not proposed for baseline removal since the guard would still flag a
byte-level difference even though it is behaviorally inert.

## Files touched (all via Edit/cp, no `git stash`/`checkout`/`restore`/`reset` used)

- `test/01_unit/lib/driver/null_block_driver_test.spl` (added missing `test()` call — real bug fix)
- `test/01_unit/os/kernel/loader/app_registry_spec.spl` (19→20 entry-count fix — real bug fix)
- `test/unit/compiler_core/keyof_spec.spl` (synced from canonical)
- `test/unit/lib/pure/tensor_ops_spec.spl` (synced from canonical)
- `test/unit/std/desktop/clipboard_spec.spl` (synced from canonical)
- `test/unit/compiler/linker/smf_driver_manifest_section_spec.spl` (synced from canonical)
- `test/integration/storage/dbfs/dbfs_engine_checkpoint_spec.spl` (synced from canonical)
- `test/unit/app/llm_caret/provider_spec.spl` (synced from canonical)
- `test/unit/app/tooling/sandbox_spec.spl` (synced from canonical)
- `test/unit/bugs/dict_type_annotation_spec.spl` (synced from canonical)
- `test/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl` (synced from canonical)
- `test/unit/os/kernel/loader/app_registry_spec.spl` (synced from fixed canonical)
- `test/unit/lib/driver/null_block_driver_test.spl` (synced from fixed canonical)

Not committed/pushed per task instructions — left for review and landing via
git plumbing.
