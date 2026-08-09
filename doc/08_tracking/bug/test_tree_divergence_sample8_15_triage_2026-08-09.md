# Test-tree divergence — sample 8 (15 pairs, `NR%65==30`)

Eighth sampling pass over `scripts/check/test_tree_divergence_baseline.txt`
(956 lines), continuing the reconciliation series (samples 1-7 covered
residues 0, offset-33-step-65, `%65==50`, `%65==15`, `%65==5`, `%65==45`,
`%65==20`). This pass used **`NR%65==30`** — non-overlapping with all prior
samples. All fixes made with the `Edit`/`Write`/`cp` tools only; no
`git stash`/`checkout`/`restore`/`reset` used anywhere in this session.
Nothing committed or pushed — left for review.

## Summary table

| # | Pair (unit/integration path) | Classification | Action | Verdict after fix |
|---|---|---|---|---|
| 1 | `app/web_stack_sample_browser_spec.spl` | Both sides had real bugs (wrong quote-escaping in canonical since `file_read` reads raw bytes so backslash-quote must be double-escaped in the spec string literal; wrong `BROWSER_PAGE` path and a stale `/items/new` literal-route assertion in shadow — route is now parameterized `{action}`) | Fixed canonical's quote-escaping, dropped the stale `/items/new` literal assertion, then synced fixed canonical → shadow | integration 2/2 both sides |
| 2 | `app/cli/native_build_arg_source_spec.spl` | Vacuous stub — shadow dropped 3 `it` blocks and added an unused import | Synced canonical → shadow | unit 5/5 both sides |
| 3 | `app/mcp_t32/mcp_t32_wsl_wrapper_spec.spl` | Cosmetic — `continue` vs `pass_dn` in a for-loop, behaviorally identical here | Left as-is | unit 28/28 both sides (already passing) |
| 4 | `app/ui/async_web_spec.spl` | Vacuous stub — shadow dropped 2 `it` blocks covering JSON cache/sniffing and HTML security headers (both header helpers verified still present and wired in `src/app/ui.web/async_server.spl`) | Synced canonical → shadow | unit 27/27 both sides |
| 5 | `compiler/backend/interpreter_backend_spec.spl` | Mixed: vacuous stub (shadow dropped 6 `it` blocks) **plus 2 genuine stale assertions in canonical** — one referenced `LoweringErrorKind.Recovered` in `driver.spl` but that check moved to `driver_hir_pipeline_lowering.spl`; the other asserted a superseded refactor pattern (`var cf_target_index = -1`) when the code has since moved to `val cf_target_hit = self.resolve_function_by_name(...)` | Fixed both stale assertions in canonical (updated file path + updated pattern to match current code), then synced → shadow | unit 11/11 both sides |
| 6 | `compiler_core/tokens_spec.spl` | Vacuous stub — shadow was empty/stubbed, canonical's source-scan assertions against `src/compiler/10.frontend/core/tokens.spl` all still hold | Synced canonical → shadow | unit 2/2 both sides |
| 7 | `compiler/mir/aop_injection_spec.spl` | Vacuous stub — shadow dropped the `Store` classification test and used `fail(...)` instead of the idiomatic `expect(false).to_equal(true)` (both work but canonical's `MirInstKind.Store` variant is verified present in `mir_instruction_kinds.spl`) | Synced canonical → shadow | unit 6/6 both sides |
| 8 | `lib/async/async_basics_spec.spl` | Vacuous stub — shadow was a badly truncated/mangled duplicate (double-hashed header, missing half the describe blocks) | Synced canonical → shadow | unit 25/25 both sides |
| 9 | `lib/common/lz4_spec.spl` | Genuine bug in shadow — truncation byte offsets (`-2`/`-6`) were wrong for the two "fails closed on truncated ... bytes" tests; canonical's (`-6`/`-10`) are correct | Synced canonical → shadow | unit 20/20 both sides |
| 10 | `lib/common/ui/wasm_hello_gui_spec.spl` | Genuine bug in shadow — asserted stale path `examples/ui/hello_wasm_gui.spl`; real file lives at `examples/06_io/ui/hello_wasm_gui.spl` (matches canonical and the actual source in `wasm_hello_gui.spl:374`) | Synced canonical → shadow | unit 19/19 both sides |
| 11 | `lib/engine/physics/physics2/backend_equiv_spec.spl` | Genuine bug in canonical — used `NodeId(raw: RawHandle.new(idx, 1))` but `NodeId.raw` is a plain `i64` field (`src/lib/common/engine/ids.spl:7`), not a `RawHandle`; shadow's `NodeId(raw: idx)` is correct | Synced shadow → canonical (reverse direction) | unit 2/2 both sides |
| 12 | `lib/nogc_async_mut/gpu/dxvk_vkd3d_dispatch_spec.spl` | Vacuous stub — shadow dropped the readback-target test; `dxvk_d3d11_create_readback_target`/`_upload_framebuffer`/`_readback_pixels` all verified present in `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl` | Synced canonical → shadow | unit 18/18 both sides |
| 13 | `lib/std/common/text_helpers_spec.spl` | Vacuous stub (shadow dropped the 84-line "search-result contract" tail) **+ genuine pre-existing bug shared by both trees**, unrelated to divergence: 7 failures (`is_ascii`/`is_printable` throw `semantic: type mismatch: comparing string with integer`; `index_of_func`/`last_index_of_func` return the lambda itself instead of its evaluated result; `expandtabs` fails) — same 7 failures on both sides before and after sync | Synced canonical → shadow (adds 13 new passing tests); left the 7 shared failures **undocumented-elsewhere so flagged here**, not fixed (looks like a systemic higher-order-function / type-coercion bug in the interpreter, out of scope for a narrow fix) | unit 95/95 total both sides, 88 passed / 7 failed (pre-existing, both sides identical) |
| 14 | `os/kernel/scheduler/scheduler_spec.spl` | Vacuous stub (shadow dropped the "green carrier scheduler integration" describe block; all `green_carrier_*` fns verified present in `src/os/kernel/scheduler/green_carrier.spl`) **+ genuine bug in shadow**: stale `x86_64_ctx.cs == 0x1B` vs canonical's correct `0x2B` (shadow additionally failed 2 tests building x86 user contexts because of this) | Synced canonical → shadow | unit 69/69 total both sides, 61 passed / 8 failed (pre-existing, both sides identical — large kernel-scheduler spec with 8 pre-existing failures spanning dequeue, exec_into, deadline CBS, notification wait/signal, wait_for zombie reap; too broad/risky to fix in this pass, flagged for a dedicated scheduler session) |
| 15 | `std/mock_phase4_spec.spl` | Cosmetic — shadow added a `get_current_state()` method wrapper around the same public `current_state` field canonical accesses directly; both produce identical pass/fail results | Synced canonical (simpler direct-field form) → shadow | unit 24/24 total both sides, 21 passed / 3 failed (pre-existing, both sides identical — `resets all mocks in composition`, `state machine with mock composition`, `manages complex multi-mock workflow` all show call-count/state values leaking or resetting incorrectly across composed mocks — looks like a mock-composition state-sharing bug, not investigated further this pass) |

## Files touched (Edit/Write/cp only)

- `test/02_integration/app/web_stack_sample_browser_spec.spl` (edited)
- `test/integration/app/web_stack_sample_browser_spec.spl` (synced)
- `test/01_unit/app/cli/native_build_arg_source_spec.spl` → `test/unit/app/cli/native_build_arg_source_spec.spl`
- `test/01_unit/app/ui/async_web_spec.spl` → `test/unit/app/ui/async_web_spec.spl`
- `test/01_unit/compiler/backend/interpreter_backend_spec.spl` (edited, 2 stale assertions fixed) → `test/unit/compiler/backend/interpreter_backend_spec.spl`
- `test/01_unit/compiler_core/tokens_spec.spl` → `test/unit/compiler_core/tokens_spec.spl`
- `test/01_unit/compiler/mir/aop_injection_spec.spl` → `test/unit/compiler/mir/aop_injection_spec.spl`
- `test/01_unit/lib/async/async_basics_spec.spl` → `test/unit/lib/async/async_basics_spec.spl`
- `test/01_unit/lib/common/lz4_spec.spl` → `test/unit/lib/common/lz4_spec.spl`
- `test/01_unit/lib/common/ui/wasm_hello_gui_spec.spl` → `test/unit/lib/common/ui/wasm_hello_gui_spec.spl`
- `test/unit/lib/engine/physics/physics2/backend_equiv_spec.spl` → `test/01_unit/lib/engine/physics/physics2/backend_equiv_spec.spl` (reverse direction)
- `test/01_unit/lib/nogc_async_mut/gpu/dxvk_vkd3d_dispatch_spec.spl` → `test/unit/lib/nogc_async_mut/gpu/dxvk_vkd3d_dispatch_spec.spl`
- `test/01_unit/lib/std/common/text_helpers_spec.spl` → `test/unit/lib/std/common/text_helpers_spec.spl`
- `test/01_unit/os/kernel/scheduler/scheduler_spec.spl` → `test/unit/os/kernel/scheduler/scheduler_spec.spl`
- `test/01_unit/std/mock_phase4_spec.spl` → `test/unit/std/mock_phase4_spec.spl`

`test/01_unit/app/mcp_t32/mcp_t32_wsl_wrapper_spec.spl` and its shadow were
left untouched (cosmetic, both already green).

## Flagged genuine bugs (not fixed this pass — out of scope / too broad)

1. **`text_helpers` interpreter bugs** (pair 13): `is_ascii`/`is_printable`
   throw `semantic: type mismatch: comparing string with integer`;
   `index_of_func`/`last_index_of_func` return the unevaluated lambda instead
   of calling it; `expandtabs` fails. Reproduce with either
   `test/01_unit/lib/std/common/text_helpers_spec.spl` or its shadow.
2. **Kernel scheduler pre-existing failures** (pair 14): 8 failures in
   `scheduler_spec.spl` — `dequeue returns the enqueued task`,
   `exec_into resolves argv0 and replaces the task image`,
   `picks admitted deadline task with earliest deadline`,
   `deadline CBS records overrun and miss traces`,
   `wake_expired_sleepers clears stale notification waiters`,
   `notification_signal stages every waiter registered on the same notification`,
   `notification_clear_waiter removes staged waiters from future drains`,
   `wait_for collects zombie child exit status and frees the slot`.
3. **Mock composition state-sharing bug** (pair 15): 3 failures in
   `mock_phase4_spec.spl` where call counts / state appear to leak or reset
   incorrectly across composed mocks (`resets all mocks in composition`,
   `uses state machine with mock composition`, `manages complex multi-mock
   workflow`).

None of these three are caused by the tree-divergence itself — same failures
reproduce identically on both canonical and shadow copies before and after
sync, confirming they are pre-existing implementation bugs, not test-tree
drift.
