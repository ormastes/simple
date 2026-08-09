# Test-tree divergence: sample 6 (15 pairs) triage (2026-08-09)

**Status:** 9 pairs reconciled (real fixes; 8 verified GREEN with `bin/simple run`,
1 fixed-but-unverifiable due to a pre-existing structural issue present in
BOTH copies). 1 pair flagged unable-to-verify (canonical itself hangs — not
fixed). 1 pair flagged as canonical itself broken/RED for a pre-existing,
unrelated reason (left as-is). 3 pairs classified cosmetic/inert, left alone.
1 pair is a false-positive baseline entry (files are byte-identical — no
divergence exists today). Baseline file
(`scripts/check/test_tree_divergence_baseline.txt`) and divergence guard
script were **not** modified. No commits made.

## Context

Sixth sampling pass against `scripts/check/test_tree_divergence_baseline.txt`
(956 lines as of this run — down from 981 at the start of the campaign,
reflecting prior sessions' reconciliations), continuing to reconcile
`test/01_unit`/`test/02_integration` (canonical) vs `test/unit`/
`test/integration` (shadow). Prior sessions covered residue classes
`NR%65==0`-ish (first 15), `offset-33-step-65`, `NR%65==50`, `NR%65==15`,
`NR%65==5` (57 pairs total across five reports). This pass uses
`NR%65==45`, non-overlapping with all five. Per instructions, skipped
`test/integration/app/app_mcp_intensive_spec.spl` (not present in this
sample) and `test/unit/lib/crypto/sha2_nist_vectors_spec.spl` (not present
in this sample either — no conflict).

Convention: canonical = `test/01_unit/**` or `test/02_integration/**`;
shadow = `test/unit/**` or `test/integration/**`. Verification used
`bin/simple run <path>` with 60-90s bounded timeouts (`bin/simple test`
was not tried directly; prior sessions established `run`/`test` are
different engines and `run` reaches real assertion execution). All edits
made with the Edit/Write tools only — no `git stash`/`checkout`/`restore`/
`reset` used anywhere in this session.

## Summary table

| # | Pair (label:relpath) | Classification | Action | Verdict |
|---|---|---|---|---|
| 1 | `integration:ffi_gen/system_test.spl` | **FIXED** — shadow was a vacuous stub (`expect(true).to_equal(true)`) replacing canonical's real content assertion | restored canonical body | canonical 1/1, shadow now 1/1 |
| 2 | `unit:app/dap/interpreter_hooks_spec.spl` | **FLAGGED — canonical itself broken**, not fixed — canonical's 2nd `it` asserts `hooks.spl` contains `"import app.io.{"`, which is no longer true of the source file; canonical itself is RED (2 of 2 examples fail). Shadow is a documented `it "skipped"` stub citing the real underlying defect (`rt_hook_enable_debugging` not found in interpreter runtime) | none — left both sides as-is | canonical 0/2 pass (2 failures); shadow left as a documented skip |
| 3 | `unit:app/mcp_unit/mcp_protocol_spec.spl` | **FIXED** — shadow imported `std.common.mcp_helpers`, a module that does **not exist** in the tree (verified via `find`); canonical correctly imports the real `app.mcp.main_lazy_json` + `app.mcp.main_lazy_protocol` modules | restored canonical's two `use` lines | canonical 20/20, shadow now 20/20 |
| 4 | `unit:app/ui/profile_spec.spl` | **FIXED** — two independent defects: (a) shadow imported the non-existent `common.ui.session` (real module is `nogc_sync_mut.ui.session`, confirmed via `find`); (b) shadow's breakpoint test used threshold `1200`, but the real source (`src/lib/common/ui/profile.spl::default_breakpoints()`) hardcodes `regular_max: 840` (Material-aligned 600/840, per the function's own docstring) — the shadow's `1200` never matched real behavior | restored canonical's import + `839`/`840` threshold values | canonical 54/54, shadow now 54/54 |
| 5 | `unit:compiler/backend/riscv_target_spec.spl` | **FLAGGED — unable to verify, not fixed** — canonical (84 lines) has 3 more `it` blocks and 2 more imports (`llvm_cross_target`, `llvm_support_matrix`) than shadow (42 lines); tried `bin/simple run` on canonical at both 60s and 90s bounded timeouts and it never reached test execution (3000+ lines of module-load warnings, no `examples,`/`VERDICT` line) — cannot confirm canonical is actually green, so did not blind-copy content into shadow | none | canonical: timeout at 90s, no verdict obtainable; shadow untouched |
| 6 | `unit:compiler/coverage/branch_coverage_19_spec.spl` | Cosmetic — canonical uses `!= nil` / `== nil`, shadow uses the equivalent `.?` / `not ... .?` postfix-optional-check operator; same semantics | left alone | — |
| 7 | `unit:compiler/mono/monomorphize_integration_spec.spl` | Cosmetic — shadow has one extra `use std.test.*` import that canonical lacks; every `it` body in both copies is a bare doc-comment `pass` (no real assertions, no use of anything from `std.test`), so the extra import is dead but harmless | left alone | — |
| 8 | `unit:lib/common/compatibility_spec.spl` | Cosmetic — canonical's header comment says `# tag: []`, shadow says `# tag: ["only-compiled"]`; grepped the whole tree for `# tag:` parsing and `"only-compiled"` usage elsewhere — neither is consumed by any runner code, so this is an inert documentation-only comment on both sides (despite the surrounding prose in both files stating the spec "requires compiled mode") | left alone | — |
| 9 | `unit:lib/common/parsers_json_core_spec.spl` | **FIXED** — shadow was missing an entire `context "nested object parsing (regression: json-parser-nested-object-nil)"` block (4 `it`s + a long regression-rationale docstring) that canonical has; canonical is a real, documented regression test tied to `doc/08_tracking/bug/string_literal_double_brace_collapse_2026-06-16.md` | inserted the missing context block verbatim | canonical 94/94, shadow now 94/94 |
| 10 | `unit:lib/common/window_protocol/input_translator_spec.spl` | **FIXED** — shadow was missing the `use common.window_protocol.window_protocol.{WmInputEvent}` import and the entire `describe "committed text"` block (Unicode IME/composed-text regression coverage) | restored missing import + describe block | canonical 8/8, shadow now 8/8 |
| 11 | `unit:lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.spl` | Cosmetic — canonical declares `var empty_px: [u32] = []` then passes the typed variable; shadow passes the `[]` literal directly to the same call site. Both engines resolve the literal's type from the parameter signature correctly here; canonical (2/2 pass) and shadow (2/2 pass) both independently verified green | left alone | canonical 2/2, shadow 2/2 (both already green) |
| 12 | `unit:lib/nogc_async_mut_noalloc/collections/fixed_array_spec.spl` | **FIXED** — shadow was a vacuous `it "skipped"` stub citing `"method 'size' not found on 'dict'"`; canonical's 2 real `it` blocks (source-content assertions against `fixed_array.spl`) run and pass cleanly, so the cited blocker no longer applies | restored canonical content | canonical 2/2, shadow now 2/2 |
| 13 | `unit:os/apps/sshd/ssh_session_shell_spec.spl` | **FIXED** — shadow retained only 3 old-style `it` blocks testing a stale shell-prompt format (`"/ $ "`, no `user@simpleos` banner-context, no CRLF/SMF-launch/unterminated-line coverage); canonical has 15 `it` blocks covering the current, correct behavior (verified real shell-prompt format, CRLF handling, SMF app-registry resolution) and canonical is fully green | replaced shadow with full canonical content (3 extra `use` imports, 1 helper fn, 12 additional `it` blocks) | canonical 15/15, shadow now 15/15 |
| 14 | `unit:os/qemu_runner_raw_image_catalog_validator_spec.spl` | **FIXED (unverifiable pass/fail)** — shadow referenced the stale flat path `scripts/make_os_disk.shs`; the real script lives at `scripts/os/make_os_disk.shs` (confirmed via `find`) — the shadow's backup/restore/shim logic operated on a path that doesn't exist. Fixed all 7 occurrences to match canonical's `scripts/os/make_os_disk.shs`. Could not get a pass/fail verdict from `bin/simple run` on **either** copy: the file's last top-level statement is a bare `rt_exit(0)` call (present in both canonical and shadow, unrelated to this divergence), which exits the process before the runner prints any `examples,`/`VERDICT` line — a pre-existing structural quirk of this spec file, not something this fix introduced or could resolve | corrected 7 stale-path occurrences to match canonical | rc=0 on both, but no test-result line obtainable from either copy (pre-existing, both-sides issue) |
| 15 | `unit:tools/ls_spec.spl` | **False-positive baseline entry** — `diff`/`cmp` show the canonical and shadow files are byte-identical today; no divergence exists to reconcile. Likely fixed by an earlier session or the baseline entry is stale | none (no divergence to fix) | — |

## Notes on verification method

- `bin/simple run <spec>` was used throughout (deployed
  `bin/release/x86_64-unknown-linux-gnu/simple`, prints the bootstrap-seed
  warning banner on every invocation, consistent with prior samples).
- For every FIXED item except #14, both the canonical pre-check and the
  post-fix shadow re-run produced an explicit
  `SPEC FILE VERDICT: ... passed=N failed=0` line, so the fix is proven
  green, not just "no crash."
- Item #5 (riscv_target_spec) and item #14 (qemu_runner spec) both hit a
  60-90s bounded timeout / early-exit ceiling before producing a verdict
  line on the canonical side — these were treated per instructions as
  "unable to verify" (item #5, left untouched) or "fixed the concrete,
  independently-confirmable bug (stale path) but couldn't get a full
  pass/fail readout" (item #14, still fixed because the path correctness
  claim was independently verified via `find`, not via the spec's own
  execution).

## Files touched this session

- `test/integration/ffi_gen/system_test.spl`
- `test/unit/app/mcp_unit/mcp_protocol_spec.spl`
- `test/unit/app/ui/profile_spec.spl`
- `test/unit/lib/nogc_async_mut_noalloc/collections/fixed_array_spec.spl`
- `test/unit/os/apps/sshd/ssh_session_shell_spec.spl`
- `test/unit/os/qemu_runner_raw_image_catalog_validator_spec.spl`
- `test/unit/lib/common/parsers_json_core_spec.spl`
- `test/unit/lib/common/window_protocol/input_translator_spec.spl`

No changes were made to `scripts/check/test_tree_divergence_baseline.txt` or
`scripts/check/check-test-tree-divergence.shs`. Nothing was committed or
pushed — left for review per instructions.
