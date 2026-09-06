# Test-tree divergence: 15-pair sample #2 triage (2026-08-08)

**Status:** 9 pairs reconciled (real fixes, verified GREEN with `build/native_probe/simple run`,
several with sabotage-round-trip proof). 1 pair flagged as unable-to-verify (canonical
itself is broken for an unrelated reason). 3 pairs classified as cosmetic-only, left
alone. 2 pairs classified as cosmetic style rename, left alone (counted in the 3 above).
Baseline file (`scripts/check/test_tree_divergence_baseline.txt`) and divergence guard
script were **not** modified.

## Context

This is a follow-up sample pass to
`doc/08_tracking/bug/test_tree_divergence_982_diagnosis_2026-08-08.md` (systemic
diagnosis) and
`doc/08_tracking/bug/test_tree_divergence_sample_15_triage_2026-08-08.md` (first
15-pair sample: 2 fixed, 1 contradictory flagged, 12 classified). Per instructions,
`app_mcp_intensive_spec.spl` (the contradictory pair from sample 1) was explicitly
skipped — another agent is investigating it independently.

**Sampling method:** sorted the 981-line baseline
(`scripts/check/test_tree_divergence_baseline.txt`), took every 65th line starting at
offset 33 (`awk 'NR%65==33'`), which is a different phase than sample 1's offset — the
two 15-pair samples do not overlap. All 15 selected pairs were fresh (not covered by
either prior doc).

**Environment:** `bin/simple` was present this session (`bin/simple test` on a single
target file hung/timed out after 30s — reason not diagnosed, consistent with sample 1's
finding that `bin/simple test` and `bin/simple run` are different engines). All
verification below uses `build/native_probe/simple run <spec>` with
`SIMPLE_MODULE_LIMIT=4000`, the same working binary/config sample 1 used and documented
under "Environment note" in that doc. Findings are attributable to this binary.

**Gotcha hit and recovered:** `git checkout -- <file>` on an uncommitted jj-tracked file
reverts to the git-tracked snapshot, which reverted one in-progress edit
(`text_formatter_spec.spl`) back to its pre-fix stub mid-session. Recovered by redoing
the edit via the `Edit` tool (never used `git checkout` again this session — all
sabotage-round-trip reverts after that point used `Edit`, not git).

## The 15 sampled pairs

| # | Pair (label:relpath) | Diff size | Classification |
|---|---|---|---|
| 1 | `integration:app/web_stack_sample_spec.spl` | 21 lines | **REAL DIVERGENT CONTENT — FIXED** (stale paths, shadow was RED) |
| 2 | `unit:app/cli/query_lsp_spec.spl` | 33 lines | **REAL DIVERGENT CONTENT — FIXED** (2 missing `it` blocks) |
| 3 | `unit:app/mcp_t32/mcp_t32_wsl_wrapper_spec.spl` | 2 lines | Cosmetic (`continue` vs `pass_dn`, same effect — last stmt in loop body) |
| 4 | `unit:app/ui/access_spec.spl` | 12 lines | **NOT FIXED — canonical itself is broken** (unrelated builder API failure, cannot verify a green restore) |
| 5 | `unit:compiler/backend/backend_api_spec.spl` | 33 lines | **REAL DIVERGENT CONTENT — FIXED** (missing GPU-contract `it` block + wrong error-message casing) |
| 6 | `unit:compiler_core/new_tokens_spec.spl` | 22 lines | **REAL DIVERGENT CONTENT — FIXED** (vacuous stub, fabricated pending_reason) |
| 7 | `unit:compiler/loader/jit_instantiator_spec.spl` | 2 lines | **REAL DIVERGENT CONTENT — FIXED** (wrong method: `.insert()` vs `.push()` on `[text]`) |
| 8 | `unit:fs_driver/mount_table_test.spl` | 40 lines | **REAL DIVERGENT CONTENT — FIXED** (stale tuple-field API `pair.0`/`pair.1` vs real struct fields `pair.mount_id`/`pair.relpath`) |
| 9 | `unit:lib/common/hpack/string_codec_spec.spl` | 4 lines | Cosmetic (local var rename `elem` → `unit`, same semantics) |
| 10 | `unit:lib/common/test_meta_spec.spl` | 24 lines | Cosmetic (`assert_true(x)` → `expect(x)`, verified identical pass/fail behavior both sides) |
| 11 | `unit:lib/diagnostics/text_formatter_spec.spl` | 19 lines | **REAL DIVERGENT CONTENT — FIXED** (vacuous stub, fabricated pending_reason) |
| 12 | `unit:lib/nogc_async_mut/async_spec.spl` | 3 lines | **REAL DIVERGENT CONTENT — FIXED** (real assertion weakened to `expect(true).to_equal(true)`) |
| 13 | `unit:lib/pure/nn_spec.spl` | 29 lines | **REAL DIVERGENT CONTENT — FIXED** (vacuous stub, fabricated pending_reason) |
| 14 | `unit:os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl` | 21 lines | **REAL DIVERGENT CONTENT — FIXED** (shadow had stale arg-based API from an abandoned memory-map refactor; canonical matches current 0-arg implementation) |
| 15 | `unit:runtime/module_closure_spec.spl` | 33 lines | **REAL DIVERGENT CONTENT — FIXED** (4 real assertions weakened to `expect(true).to_equal(true)`) |

**9 fixed, 1 flagged not fixed, 5 cosmetic (left alone).**

## Fixed pairs — detail and verification

### 1. `integration:app/web_stack_sample_spec.spl`

Shadow (`test/integration/...`) referenced stale paths:
`examples/web_stack_sample/app.sdn` (does not exist — confirmed via `ls`, exit 2) and
`"build/web_stack_sample/sample.sdn"` as the expected `simpledb_path` value, vs
canonical's `examples/06_io/web_stack_sample/app.sdn` (exists) and
`"var/lib/web_stack_sample/sample.sdn"` (confirmed present in the actual `.sdn` file via
`grep`). Confirmed the shadow copy was **currently RED for the wrong reason** before the
fix: 3 of 4 examples failed (file-not-found style failures), vs canonical's 1
pre-existing failure (`fn post_new_item` genuinely missing from
`src/app/web_stack_sample/app.spl` — confirmed by `grep`, 0 matches). Per the testing
rule "a correct spec that fails is a legitimate artifact," the canonical's one failure
was left as-is (it documents a real, separate implementation gap, out of scope for this
divergence-reconciliation pass). Fixed only the 2 path/value lines that were stale in
the shadow copy; left the `extern fn`-style read helper as-is (cosmetic, functionally
equivalent to canonical's `use std.io_runtime.{file_read}`).

- **Before:** 4 examples, 3 failures.
- **After:** 4 examples, 1 failure (now matches canonical's real, pre-existing,
  intentionally-red assertion about `post_new_item`).

### 2. `unit:app/cli/query_lsp_spec.spl`

Shadow was missing 2 `it` blocks canonical has: "semantic token range flags use guarded
integer parsing" and "position arguments use guarded integer parsing" — both regression
gates checking that `src/app/cli/query.spl`,
`src/app/cli/_QueryVisibility/query_commands.spl`, and
`src/app/cli/query_rich_common.spl` use the guarded `*_nonnegative_int_or_zero(...)`
parsers instead of raw `.to_int()`. Verified all referenced symbols exist via `grep` on
the 3 source files before porting.

- **After:** all 24 examples across the file green (7 describe blocks, each printing its
  own summary; 0 failures anywhere).

### 3. `unit:compiler/backend/backend_api_spec.spl`

Shadow was missing an entire `it` block ("reports GPU artifact target contracts for CUDA
HIP OpenCL and Vulkan", 17 assertions on `BackendKind`/`CodegenTarget` GPU helpers) and
had a wrong-cased assertion (`"Backend Cranelift does not support target X86"` vs
canonical's `"Backend cranelift does not support target x86"` — the source template
lower-cases via `.to_text()`, confirmed canonical runs green). Ported both.

- **Before (shadow):** untested (content missing/wrong).
- **After:** 5 examples, 0 failures (matches canonical exactly, byte-identical).

### 4. `unit:compiler_core/new_tokens_spec.spl`

Shadow was a vacuous `slow_it "skipped"` stub with `pending_reason = "imports compiler
modules - causes OOM via numbered directory resolution"`. The stated reason does not
match the file's actual content: canonical only does `file_read(...)` on
`src/compiler/10.frontend/core/tokens.spl` as plain text (no `use compiler.*` import at
all) — same fabricated-stub-reason pattern flagged in sample 1 for `semver_spec.spl`.
Verified the asserted constants (`TOK_KW_STATIC_FOR = 201`, `TOK_KW_COMPTIME = 202`,
`TOK_KW_MIXIN = 203`) are present in the real source file via `grep`, then confirmed
canonical runs green before porting.

- **After:** 2 examples, 0 failures.

### 5. `unit:compiler/loader/jit_instantiator_spec.spl`

One-line real bug: shadow called `jit.in_progress.insert("cycle_fn")` where
`in_progress: [text]` is a plain array (`.push()` is the append method; `.insert()` is
not valid on `[text]` in this codebase — Dict has `.insert()`, arrays don't). Confirmed
by grepping the actual field type in `src/compiler/loader/jit_instantiator.spl:165`. The
shadow copy was previously RED with `semantic: type mismatch: cannot convert string to
int` on exactly this line — canonical passes. Fixed the one word.

- **Before:** 6 examples, 2 failures (1 shared with canonical — pre-existing, unrelated
  `finds metadata-backed symbols` failure; 1 caused by the bad `.insert()` call).
- **After:** 6 examples, 1 failure — now exactly matches canonical's pre-existing,
  unrelated failure (out of scope for this pass).

### 6. `unit:fs_driver/mount_table_test.spl`

Larger real divergence: shadow used a stale tuple-indexing API (`pair.0`, `pair.1`) on
`mt.resolve(...)`'s return value, but the real return type
(`MountResolution(mount_id: MountId, relpath: Path)`, confirmed in
`src/lib/nogc_async_mut/fs_driver/mount_table.spl:228-238`) is a named struct — `.0`/`.1`
field access on a named struct is invalid/wrong here. This alone caused 4 real failures
in the shadow copy (`lookup finds the mounted entry`, `lookup with child path finds root
mount`, both `resolve(...)` tests) while canonical (using `.mount_id`/`.relpath`) was
fully green. The rest of the diff (`"/"` → `root_path()`, `fail(...)` →
`expect(false).to_equal(true)`) is the same style-normalization sample 1 already
classified as behaviorally equivalent. Copied canonical's content verbatim (`cp`,
verified byte-identical with `diff`).

- **Before (shadow):** 13 examples total across 4 describe blocks, 4 failures.
- **After:** 13 examples, 0 failures — matches canonical exactly.

### 7. `unit:lib/diagnostics/text_formatter_spec.spl`

Vacuous `slow_it "skipped"` stub (`pending_reason = "module
'compiler_shared.diagnostics' not resolvable"`) replacing 2 real `it` blocks that assert
the presence of 10 named functions (`pad_right`, `pad_left`, `sep_line`,
`format_tokens_k`, `format_token_usage_text`, etc.) in
`src/lib/nogc_async_mut/llm_diagnostics/formatters/text_formatter.spl`. All 10 confirmed
present via `grep` before porting. **Full sabotage round-trip performed:** GREEN (2
examples, 0 failures) → sabotage (renamed `pad_right` → `pad_right_SABOTAGE` in the
assertion string) → RED (1 failure, correct assertion-mismatch message) → reverted via
`Edit` → GREEN again, confirmed byte-identical to canonical.

### 8. `unit:lib/nogc_async_mut/async_spec.spl`

One `it` block ("iterates over async streams") had its real assertion
(`select([HostFuture.pending(), HostFuture.ready(42)]).is_ready() == true`) replaced
with `expect(true).to_equal(true)` plus a comment claiming "Needs async fn* syntax -
stub passes trivially." Verified `HostFuture.pending()`/`HostFuture.ready()` exist in
`src/lib/nogc_async_mut/async_host/future.spl` and canonical runs fully green (5
describe blocks, 0 failures) before porting — the "needs new syntax" comment does not
match reality; the real assertion already works today.

- **After:** matches canonical exactly (5 describe-block summaries, all 0 failures).

### 9. `unit:lib/pure/nn_spec.spl`

Same fabricated-stub pattern as #4/#7 (`pending_reason = "timeout - module loading
exceeds 60s"`). Canonical has 2 real `it` blocks asserting the structure of
`src/os/ml/model.spl` (trait `Module`, `class GpuLinear`, `class GpuReLU`, `class
GpuSequential`, and their methods/fields) — all confirmed present via `grep`; canonical
runs in well under any 60s timeout in this session's runs. **Full sabotage round-trip
performed:** GREEN (2 examples, 0 failures) → sabotage (`trait Module:` →
`trait Module_SABOTAGE:`) → RED (1 failure, correct assertion-mismatch) → reverted via
`Edit` → GREEN again, confirmed byte-identical to canonical.

### 10. `unit:os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl`

**Direction note:** the diff's `-`/`+` sides are easy to misread here — canonical
(`test/01_unit/...`, the `-` side) is the *simpler* no-arg-call version and is the one
that's currently correct; shadow (`test/unit/...`, the `+` side) is the one carrying
extra `kria_memory_map_new()`/`litex_memory_map_new()` plumbing from an apparent
memory-map-parameterization refactor that was **not** landed in
`src/os/kernel/boot/riscv_noalloc_handoff.spl` — `grep` confirms
`riscv_noalloc_layout_from_kria()`/`riscv_noalloc_layout_from_litex()` are still 0-arg
today. Confirmed empirically: canonical runs 8/8 green; shadow (pre-fix) failed all 8
examples with `semantic: function expects 0 argument(s), but more were provided`. Copied
canonical's content verbatim.

- **Before (shadow):** 8 examples, 8 failures.
- **After:** 8 examples, 0 failures — matches canonical exactly.

### 11. `unit:runtime/module_closure_spec.spl`

4 real assertions across 4 `it` blocks weakened to `expect(true).to_equal(true)`,
including one (`documents the difference: nested fn vs module fn`) that dropped a real
functional check (`module_state_reset()`, `module_state_touch("module-fn")`,
`module_state_label()` — all defined locally in the same file, self-contained, no
external deps). Verified canonical runs fully green (10 examples across 4 describe
blocks, 0 failures) before porting verbatim.

- **After:** matches canonical exactly, all 10 examples green.

## Not fixed — flagged

### `unit:app/ui/access_spec.spl`

Real divergence exists (shadow's `use nogc_sync_mut.ui.session.{UISession}` →
`use common.ui.session.{UISession}` is a broken import — `common/ui/session.spl` does
not exist, only `nogc_sync_mut/ui/session.spl` does; shadow also drops the
`ui_access_empty_snapshot` import and a trailing 4-line assertion block). However,
**canonical itself is currently almost entirely RED** (10 of 11 examples fail) with an
unrelated pre-existing error: `semantic: function expects argument for parameter
'children', but none was provided` — a builder-API (`column`/`build_tree`) signature
mismatch affecting nearly the whole file, unrelated to the session/access-store logic
under test. Since the task rule requires actually running the ported result to confirm
a green pass, and there is no green reference to restore *to* here, this was flagged
rather than blind-ported. Recommend a dedicated lane investigate the `column`/
`build_tree` "children" parameter regression first; the shadow's import-path/content gap
can be reconciled once canonical itself is green again.

## Cosmetic / equivalent-semantics — left alone

- `unit:app/mcp_t32/mcp_t32_wsl_wrapper_spec.spl` — `continue` (canonical) vs `pass_dn`
  (shadow) as the last statement of a `for`-loop's `if`/`else if` chain with nothing
  following it in the loop body; both fall through to the next iteration identically.
- `unit:lib/common/hpack/string_codec_spec.spl` — local variable renamed `elem` →
  `unit` inside a helper function; no behavior difference.
- `unit:lib/common/test_meta_spec.spl` — `assert_true(x)` (canonical) vs `expect(x)`
  (shadow) applied uniformly across 12 sites, all on trivially-`true` placeholder
  values. Verified both sides produce identical example counts and 0 failures across
  all 5 describe blocks before classifying as cosmetic.

## Files changed this session

- `test/integration/app/web_stack_sample_spec.spl`
- `test/unit/app/cli/query_lsp_spec.spl`
- `test/unit/compiler/backend/backend_api_spec.spl`
- `test/unit/compiler_core/new_tokens_spec.spl`
- `test/unit/compiler/loader/jit_instantiator_spec.spl`
- `test/unit/fs_driver/mount_table_test.spl`
- `test/unit/lib/diagnostics/text_formatter_spec.spl`
- `test/unit/lib/nogc_async_mut/async_spec.spl`
- `test/unit/lib/pure/nn_spec.spl`
- `test/unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl`
- `test/unit/runtime/module_closure_spec.spl`

Baseline file was **not** touched. Re-running `sh scripts/check/check-test-tree-divergence.shs`
after this session's edits reports `10 new, 12 fixed-but-still-baselined` — the "12"
matches this session's 9 newly-reconciled pairs (`web_stack_sample_spec.spl` doesn't
appear in that list because it was only partially reconciled — the cosmetic
`extern fn` vs `use std.io_runtime` style difference was deliberately left in place, so
the pair is still byte-diverged from canonical, correctly) plus the 2 pairs sample 1
already fixed (`semver_spec.spl`, `aes128_gcm_nist_vectors_spec.spl`) that were likewise
never removed from the baseline. The "10 new" divergences reported in the same run
(`app/wine_hello_command_spec.spl`, `app/arch_check_spec.spl`, etc.) were **not**
touched by this session — they are pre-existing drift from concurrent sessions editing
the shared working copy, confirmed unrelated to any file this session modified.
