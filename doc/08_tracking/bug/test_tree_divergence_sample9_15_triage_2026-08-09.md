# Test-tree divergence — sample 9 (15 pairs, `NR%65==40`)

Ninth sampling pass over `scripts/check/test_tree_divergence_baseline.txt`
(956 lines), continuing the reconciliation series (samples 1-8 covered
residues 0, offset-33-step-65, `%65==50`, `%65==15`, `%65==5`, `%65==45`,
`%65==20`, `%65==30`). This pass used **`NR%65==40`** — non-overlapping with
all prior samples. All fixes made with the `Edit`/`Write`/`cp` tools only; no
`git stash`/`checkout`/`restore`/`reset` used anywhere in this session.
Nothing committed or pushed — left for review.

Before starting, `git fetch origin main -q` was run and every one of the 30
canonical/shadow file paths involved was verified to have `sha1sum` identical
between the live working copy and `origin/main` — the shared-WC-clobbering
hazard did not affect this sample's starting state.

## Summary table

| # | Pair (unit/integration path) | Classification | Action | Verdict after fix |
|---|---|---|---|---|
| 1 | `compiler/native_backend_e2e_spec.spl` (integration) | Vacuous stub — shadow's "compile" test replaced a real oracle (`not source.contains(...)`) with a hardcoded `true`, and commented out the negative-compile assertions in another `it`, replacing them with a placeholder `expect(true).to_equal(true)` | Synced canonical → shadow | integration 12/12 both sides |
| 2 | `app/dap/dap_spec.spl` | Both: shadow was entirely skipped (`it "skipped"` stub citing an unrelated cast issue) **and canonical had a genuine stale assertion** — `expect(protocol).to_contain("class Variable:")` but the actual class in `src/lib/nogc_sync_mut/dap/protocol.spl:164` is `class DapVariable:` | Fixed canonical's stale class name, then synced fixed canonical → shadow | unit 2/2 both sides (was 1/2 failing before the fix) |
| 3 | `app/mcp_unit/error_handler_spec.spl` | Vacuous stub — shadow softened several `case nil:` branches to `pass_do_nothing  # may not trigger in interpreter mode` instead of canonical's real `expect(...).to_be_greater_than(...)` assertions, and used `expect(false).to_equal(true)` in place of canonical's `fail(...)` (same effect) | Synced canonical → shadow | unit 34/34 both sides |
| 4 | `app/ui/headless_app_spec.spl` | Genuine bug in shadow — asserted stale path `examples/ui/minimal.ui.sdn`; the real file lives at `examples/06_io/ui/minimal.ui.sdn` (verified via `ls`, matches canonical) | Synced canonical → shadow | unit 8/8 both sides |
| 5 | `compiler/backend/native/encode_riscv64_spec.spl` | Vacuous stub — shadow dropped ~30 of ~35 `it` blocks (all RV64 MachInst/branch/jump/immediate/patch coverage), keeping only 5 scalar-bitmanip tests | Synced canonical → shadow | unit 37/37 both sides |
| 6 | `compiler/coverage/branch_coverage_13_spec.spl` | Cosmetic — shadow used `.?`/`not x.?` postfix-option-check sugar where canonical used `!= nil`/`== nil`; behaviorally identical here (both green before touching) | Synced canonical → shadow for consistency | unit 78/78 both sides |
| 7 | `compiler/mir_opt/predicate_promote_spec.spl` | Cosmetic — shadow constructed `MirModule(functions: {})` relying on default field values; canonical fully specifies all fields (`statics`, `constants`, `types`) | Synced canonical (more explicit) → shadow | unit 11/11 both sides |
| 8 | `lib/common/auto_comprehensive_13_spec.spl` | Cosmetic — same `.?` vs `!= nil` pattern as pair 6, plus trailing whitespace | Synced canonical → shadow | unit 30/30 both sides |
| 9 | `lib/common/mock_spec.spl` | Genuine bug in shadow — the `Mock.call` sequence-stub logic mutated `stub.sequence_idx` on a per-iteration loop copy of a value-typed struct (never written back to `self.stubs`), so repeated calls would not actually advance the stored sequence index across invocations; canonical instead derives the index from `recorder.call_count(method) - 1`, which reads correctly-updated state each call | Synced canonical (correct indexing) → shadow | unit 41/41 both sides |
| 10 | `lib/common/web/browser_session_node_host_spec.spl` | Two-way vacuous drift — canonical was missing shadow's "denies direct Node host syntax in browser mode" test (7 assertions via a `_browser_eval_is_error` helper) while shadow was missing canonical's two tests ("does not install Node globals on BrowserSession page runtimes" and "keeps Node support available only through explicit JS engine APIs") | **Merged**: added the missing helper fn + `it` block from shadow into canonical, verified 7/7, then synced merged canonical → shadow | unit 7/7 both sides (canonical grew from 6→7, shadow grew from 5→7) |
| 11 | `lib/gc_async_mut/db/dbfs_engine/dbfs_engine_facade_spec.spl` | Cosmetic — `fail("...")` vs `expect(false).to_equal(true)`, single-test file, both already green | Left as-is | unit 1/1 both sides (unchanged, already passing) |
| 12 | `lib/nogc_async_mut/mcp/dispatch_spec.spl` | Vacuous stub — shadow used the terser `AuthorityToken.mock(...)` 3-arg factory and dropped canonical's extra `expect reply to_contain "\"body\":\"ok\""` assertion on the third test | Synced canonical (fuller constructor + extra assertion) → shadow | unit 4/4 both sides |
| 13 | `os/apps/browser_demo_launcher_lifecycle_spec.spl` | Vacuous stub — shadow dropped the "rejects a client destroying another client's window" `it` block entirely (REQ-WEB-BROWSER-014/016 cross-tenant window-destroy authorization test) | Synced canonical → shadow | unit 5/5 both sides |
| 14 | `os/proxy/socks5_spec.spl` | Vacuous stub — shadow replaced canonical's real `expect(reason).to_equal(Socks5Error.UnexpectedEnd)` assertions (×4 sites) with `expect(true).to_equal(true)`, and `fail(...)` calls with `expect(false).to_equal(true)` (same effect, no coverage loss on those) | Synced canonical → shadow | unit 30/30 both sides |
| 15 | `std/spec_framework_spec.spl` | Vacuous stub — shadow replaced two real assertions (`expect(context_name).to_contain("context")`, `expect(enabled).to_equal(not false)`) with bare `expect(true).to_equal(true)` placeholders | Synced canonical → shadow | unit 16/16 both sides |

## Files touched (Edit/Write/cp only)

- `test/01_unit/app/dap/dap_spec.spl` (edited: `class Variable:` → `class DapVariable:`) → `test/unit/app/dap/dap_spec.spl` (synced)
- `test/01_unit/app/mcp_unit/error_handler_spec.spl` → `test/unit/app/mcp_unit/error_handler_spec.spl`
- `test/01_unit/app/ui/headless_app_spec.spl` → `test/unit/app/ui/headless_app_spec.spl`
- `test/01_unit/compiler/backend/native/encode_riscv64_spec.spl` → `test/unit/compiler/backend/native/encode_riscv64_spec.spl`
- `test/01_unit/compiler/coverage/branch_coverage_13_spec.spl` → `test/unit/compiler/coverage/branch_coverage_13_spec.spl`
- `test/01_unit/compiler/mir_opt/predicate_promote_spec.spl` → `test/unit/compiler/mir_opt/predicate_promote_spec.spl`
- `test/01_unit/lib/common/auto_comprehensive_13_spec.spl` → `test/unit/lib/common/auto_comprehensive_13_spec.spl`
- `test/01_unit/lib/common/mock_spec.spl` → `test/unit/lib/common/mock_spec.spl`
- `test/01_unit/lib/common/web/browser_session_node_host_spec.spl` (edited: merged in shadow's unique test) → `test/unit/lib/common/web/browser_session_node_host_spec.spl` (synced)
- `test/01_unit/lib/nogc_async_mut/mcp/dispatch_spec.spl` → `test/unit/lib/nogc_async_mut/mcp/dispatch_spec.spl`
- `test/01_unit/os/apps/browser_demo_launcher_lifecycle_spec.spl` → `test/unit/os/apps/browser_demo_launcher_lifecycle_spec.spl`
- `test/01_unit/os/proxy/socks5_spec.spl` → `test/unit/os/proxy/socks5_spec.spl`
- `test/01_unit/std/spec_framework_spec.spl` → `test/unit/std/spec_framework_spec.spl`
- `test/02_integration/compiler/native_backend_e2e_spec.spl` → `test/integration/compiler/native_backend_e2e_spec.spl`

`test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_engine_facade_spec.spl` and
its shadow were left untouched (cosmetic, both already green, single test).

## Flagged genuine bugs — not fixed this pass

None of this sample's genuine bugs required leaving anything RED. All were
fixable within the narrow scope of syncing the test-tree divergence:

1. **`app/dap/dap_spec.spl` stale class-name assertion** (pair 2) — already
   fixed in this pass (canonical was wrong, `DapVariable` vs `Variable`).
2. **`app/ui/headless_app_spec.spl` stale fixture path** (pair 4) — already
   fixed (shadow was wrong, `examples/ui/...` vs the real
   `examples/06_io/ui/...`).
3. **`lib/common/mock_spec.spl` sequence-index mutation bug** (pair 9) —
   already fixed by adopting canonical's `call_count`-derived indexing over
   shadow's loop-local struct-field mutation that never persisted. Worth a
   note for future sweeps: this is another instance of the "value-typed
   struct field mutated inside a `for` loop doesn't write back to the
   underlying collection" pitfall — not confirmed against a compiler-level
   bug report this pass, but consistent with `feedback_arrays_value_types.md`
   type semantics documented in memory.

No pre-existing failures identical on both trees were found in this sample —
every pair in `NR%65==40` reached a fully-green verdict (or was already green
and cosmetic) after syncing/fixing.
