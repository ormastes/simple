# Test-tree divergence — sample 10 (15 pairs, `NR%65==10`)

Tenth sampling pass over `scripts/check/test_tree_divergence_baseline.txt`
(956 lines), continuing the reconciliation series (samples 1-9 covered
residues 0, offset-33-step-65, `%65==50`, `%65==15`, `%65==5`, `%65==45`,
`%65==20`, `%65==30`, `%65==40`). This pass used **`NR%65==10`** —
non-overlapping with all prior samples. All fixes made with the
`Edit`/`Write`/`cp` tools only; no `git stash`/`checkout`/`restore`/`reset`
used anywhere in this session. Nothing committed or pushed — left for review.

Before starting, `git fetch origin main -q` was run and all 30
canonical/shadow file paths involved were verified `sha1sum`-identical
between the live working copy and `origin/main`.

**Environment note:** this pass ran under heavy concurrent load (up to 48
`bin/simple` processes observed via `ps aux`, consistent with the
shared-WC/parallel-agent-session hazard documented in memory). Several
`bin/simple test` invocations timed out mid-compile (before reaching test
execution) even at 400s. Where a live post-sync re-run could not complete,
verification instead relies on (a) the canonical copy's live, completed
`Results:` line captured before the sync, and (b) `diff -q`/directory-diff
confirming the shadow copy is now byte-identical to that already-verified
canonical content — i.e. functional equivalence by construction. This is
flagged per-row below.

## Summary table

| # | Pair (unit/integration path) | Classification | Action | Verdict after fix |
|---|---|---|---|---|
| 1 | `app/loader_exec_memory_spec.spl` (integration) | Cosmetic — shadow used `expect(x)` bare-truthy form where canonical used `assert_true(x)`, behaviorally equivalent | Synced canonical → shadow | Both sides pre-existing RED: `error: test-runner: no examples executed` (infra/harness issue with this native-exec-memory integration spec, unrelated to the diff) — **flagged, left RED** |
| 2 | `rendering/pixel_verify_debug.spl` (integration) | Cosmetic — only a build-instructions comment differed (`core-c-bootstrap` vs `rust-hosted` runtime-bundle flag in a `# Build:` comment) | Synced canonical → shadow | Both sides pre-existing RED: `error: semantic: Cannot resolve module: common.render_scene.executor` — the module `src/lib/common/render_scene/executor.spl` does not exist (confirmed via `find`) — **flagged, left RED, pre-existing, unrelated to divergence** |
| 3 | `app/io/file_shell_exec_spec.spl` | Vacuous stub — shadow was entirely skipped (`it "skipped"` citing "functions/imports not available") with all 5 real tests commented out | Synced canonical → shadow | unit 6/6 both sides (live-verified post-sync) |
| 4 | `app/todo/todo_parser_spec.spl` | **Genuine bug in shadow** — shadow added an unused `use tooling.TodoItem.*` import that doesn't resolve (`Module "tooling" does not export 'TodoItem'`), breaking the file; canonical has no such import | Synced canonical (drops the broken import) → shadow | unit 1/1 both sides (live-verified; shadow was 0/1 failing before fix) |
| 5 | `browser_engine/margin_collapse_spec.spl` | Cosmetic — only a `# @cover ...` coverage-annotation comment differed | Synced canonical → shadow | Both sides pre-existing RED: `semantic: function collapse_margins_signed not found` — the spec imports from `...browser_engine.layout`, but `collapse_margins_signed` is actually defined in `...browser_engine.layout_m14_types` (not re-exported by `layout.spl`) — **flagged, left RED, pre-existing bug identical on both trees, out of narrow sync scope** |
| 6 | `compiler_core/file_class_introspection_spec.spl` | Vacuous stub — shadow skipped (citing "OOM via numbered directory resolution"), dropping 4 real source-introspection assertions | Synced canonical → shadow | Canonical live-verified 5/5 pre-sync; post-sync shadow re-run timed out repeatedly under heavy system load (400s, never reached test execution) — verified byte-identical via `diff -q` instead |
| 7 | `compiler/lexer/lexer_comprehensive_spec.spl` | Vacuous stub — shadow skipped (citing same stale reason), dropping 2 real lexer-source assertions | Synced canonical → shadow | Canonical live-verified 2/2 pre-sync; shadow now byte-identical (`diff -q` clean) |
| 8 | `compiler/type_inference/dim_constraints_spec.spl` | Vacuous stub — shadow skipped (citing "OOM via numbered directory resolution") | Synced canonical → shadow | Canonical live-verified 2/2 pre-sync; post-sync shadow re-run timed out under load — verified byte-identical via `diff -q` |
| 9 | `lib/common/exp/run_spec.spl` | Vacuous stub — shadow skipped (citing "std.exp.* path unresolvable") | Synced canonical → shadow | Canonical live-verified 1/1 pre-sync; shadow now byte-identical |
| 10 | `lib/common/pure/utils_spec.spl` | Vacuous stub — shadow skipped (citing "assertion failures - runtime behavior differs") | Synced canonical → shadow | Canonical live-verified 2/2 pre-sync; post-sync shadow re-run timed out under load — verified byte-identical via `diff -q` |
| 11 | `lib/database/feature_utils_extract_spec.spl` | Vacuous stub — shadow skipped (citing "function 'extract_quoted_string' not found in interpreter runtime") | Synced canonical → shadow | Canonical live-verified 2/2 pre-sync; shadow now byte-identical |
| 12 | `lib/hardware/rv64gc_rtl/core64_integration_spec.spl` | Vacuous stub — shadow dropped the whole "Core64 SYSTEM trap returns" describe block (MRET/SRET/SFENCE.VMA core-update tests), the MRET-decode test, and weakened `trap64_mret`'s U-mode-return test from exact `target_mode`/`return_pc`/`mstatus` checks to a loose `to_be_less_than(4)` | Synced canonical (fuller/exact) → shadow | Canonical live-verified 32/35 (3 pre-existing failures: `function core64_step not found` ×2 and `AC-1: core64_init zeroes all CSRs` expecting 8192==0 — confirmed `core64_step` is genuinely absent from `src/lib/hardware/rv64gc_rtl/core.spl`; both canonical and shadow import it identically, so this is pre-existing on both trees, unrelated to the divergence) — **flagged, left RED**; shadow now byte-identical to canonical |
| 13 | `lib/nogc_sync_mut/http/auth/digest_spec.spl` | **Genuine bug in shadow** — shadow asserted `http_digest_make_response(...)` returns `""` for `SHA-512-256` ("not yet implemented"), but the implementation (`src/lib/nogc_sync_mut/http/auth/digest.spl:70-71`) has supported SHA-512-256 via `sha512_256_bytes` all along; canonical correctly asserts full support | Synced canonical (correct, matches implementation) → shadow | unit 14/14 both sides — canonical live-verified 14/14 including the SHA-512-256 test; shadow now byte-identical |
| 14 | `os/kernel/arch/riscv64_trap_model_spec.spl` | **Genuine bug in shadow** — shadow asserted `create_rv64_user_context(...).a0 == 11` (the passed `arg`), but the implementation's docstring (`src/os/kernel/arch/riscv64/trap_model.spl:101-108`) states "`a0` is NOT used for the initial arg — libc's `_start` reads argc/argv from the stack"; canonical correctly asserts `a0 == 0`. Shadow also dropped canonical's `RV64_SSTATUS_FS_MASK`/`RV64_CONTEXT_BYTES==544` checks | Synced canonical (correct, matches implementation + docstring) → shadow | unit 6/6 both sides — canonical live-verified 6/6; shadow now byte-identical |
| 15 | `runtime/module_init_spec.spl` | Vacuous stub — shadow replaced two real assertions (`expect(my_init()).to_equal(0)`, `expect(my_teardown()).to_equal(0)`) with a placeholder `expect(true).to_equal(true)` | Synced canonical → shadow | Canonical live-verified 2/2 pre-sync; shadow now byte-identical |

## Files touched (Edit/Write/cp only)

- `test/02_integration/app/loader_exec_memory_spec.spl` → `test/integration/app/loader_exec_memory_spec.spl`
- `test/02_integration/rendering/pixel_verify_debug.spl` → `test/integration/rendering/pixel_verify_debug.spl`
- `test/01_unit/app/io/file_shell_exec_spec.spl` → `test/unit/app/io/file_shell_exec_spec.spl`
- `test/01_unit/app/todo/todo_parser_spec.spl` → `test/unit/app/todo/todo_parser_spec.spl`
- `test/01_unit/browser_engine/margin_collapse_spec.spl` → `test/unit/browser_engine/margin_collapse_spec.spl`
- `test/01_unit/compiler_core/file_class_introspection_spec.spl` → `test/unit/compiler_core/file_class_introspection_spec.spl`
- `test/01_unit/compiler/lexer/lexer_comprehensive_spec.spl` → `test/unit/compiler/lexer/lexer_comprehensive_spec.spl`
- `test/01_unit/compiler/type_inference/dim_constraints_spec.spl` → `test/unit/compiler/type_inference/dim_constraints_spec.spl`
- `test/01_unit/lib/common/exp/run_spec.spl` → `test/unit/lib/common/exp/run_spec.spl`
- `test/01_unit/lib/common/pure/utils_spec.spl` → `test/unit/lib/common/pure/utils_spec.spl`
- `test/01_unit/lib/database/feature_utils_extract_spec.spl` → `test/unit/lib/database/feature_utils_extract_spec.spl`
- `test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl` → `test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl`
- `test/01_unit/lib/nogc_sync_mut/http/auth/digest_spec.spl` → `test/unit/lib/nogc_sync_mut/http/auth/digest_spec.spl`
- `test/01_unit/os/kernel/arch/riscv64_trap_model_spec.spl` → `test/unit/os/kernel/arch/riscv64_trap_model_spec.spl`
- `test/01_unit/runtime/module_init_spec.spl` → `test/unit/runtime/module_init_spec.spl`

No files were left untouched in this sample — all 15 pairs had a real
divergence to sync (unlike some prior samples, none were "already identical"
or purely cosmetic-with-no-action).

## Flagged genuine bugs — not fixed this pass

Three pre-existing failures were found that are **identical on both
canonical and shadow trees** (not caused by, or fixable within scope of, the
divergence-sync itself). Per the testing rule, these are left RED and
flagged rather than weakened or force-passed:

1. **`app/loader_exec_memory_spec.spl` (integration)** — `error:
   test-runner: no examples executed`. The spec never reaches its `it`
   blocks; looks like a harness/child-binary issue for this
   native-exec-memory integration spec specifically. Needs separate
   investigation of the integration-test harness for native-alloc specs.
2. **`rendering/pixel_verify_debug.spl` (integration)** — `error: semantic:
   Cannot resolve module: common.render_scene.executor`. Confirmed via `find`
   that `src/lib/common/render_scene/executor.spl` does not exist (only
   `box_types.spl`, `css_types.spl`, `matrix4.spl`, `office_style_resolver.spl`,
   `paint_types.spl`, `scene.spl`, `scene_to_canvas2d_json.spl` are present).
   This spec references a module that was apparently never created or was
   removed; needs its own bug filed to either add the module or repoint the
   import.
3. **`browser_engine/margin_collapse_spec.spl`** — `semantic: function
   collapse_margins_signed not found`, 8/8 failing on both trees. The
   function is real and implemented (`src/lib/gc_async_mut/gpu/browser_engine/layout_m14_types.spl:59`),
   but the spec imports it from
   `std.gc_async_mut.gpu.browser_engine.layout`, which does not define or
   re-export it. A one-line fix (repoint the `use` import, or a re-export in
   `layout.spl`) is plausible but was left alone since it goes beyond the
   narrow scope of divergence-syncing and risks unintended side effects on
   `layout.spl`'s export surface — flagging for a follow-up bug/fix instead.
4. **`lib/hardware/rv64gc_rtl/core64_integration_spec.spl`** — 3 of 35
   examples fail on canonical (now also on the synced shadow): `function
   core64_step not found` (×2) and `AC-1: core64_init zeroes all CSRs`
   (`expected 8192 to equal 0`). Confirmed `core64_step` genuinely does not
   exist in `src/lib/hardware/rv64gc_rtl/core.spl` (only `core64_init` and
   internal helpers are present) — both canonical and shadow's `use` imports
   name it identically, so this is a pre-existing gap in the RTL core
   module's public API, not something introduced by this divergence-sync
   pass.

Two genuine bugs **were** fixed (adopting canonical, which matches the
actual implementation, over shadow's stale/wrong assertions):

- **`http/auth/digest_spec.spl`** — shadow wrongly asserted SHA-512-256 is
  unimplemented; the implementation has supported it via `sha512_256_bytes`
  all along.
- **`os/kernel/arch/riscv64_trap_model_spec.spl`** — shadow wrongly asserted
  `a0` carries the initial user-context argument; the implementation's own
  docstring says `a0` is explicitly NOT used for that (stack-based ABI).
- **`app/todo/todo_parser_spec.spl`** — shadow's extra `use tooling.TodoItem.*`
  import didn't resolve, breaking an otherwise-trivial spec.
