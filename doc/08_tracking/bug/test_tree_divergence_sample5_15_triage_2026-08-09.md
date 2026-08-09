# Test-tree divergence: sample 5 (15 pairs) + Part A old pending items (2026-08-09)

Fifth sampling pass against `scripts/check/test_tree_divergence_baseline.txt`,
continuing the reconciliation of `test/01_unit` (canonical) vs `test/unit`
(shadow) and `test/02_integration` (canonical) vs `test/integration` (shadow).
Prior sessions covered residue classes `NR%65==0`-ish (first 15),
`offset-33-step-65`, `NR%65==50`, `NR%65==15` (41 pairs total, see the four
prior `test_tree_divergence_sample*_triage_2026-08-08.md` reports). This pass
uses `NR%65==5`, non-overlapping with all four.

## Part A — old pending items

### 1. `mailbox_spec.spl` (`test/01_unit/lib/nogc_async_mut/` vs `test/unit/lib/nogc_async_mut/`)

- Canonical (18 lines): real regression spec for the 2026-08-07 ambiguous
  `Mailbox` package-export Stage-2 build failure — pins (a) the dead
  `src/lib/nogc_async_mut/mailbox.spl` stays deleted and (b) the sole
  surviving `Mailbox` symbol is `mailbox_actor.spl`'s.
- Shadow (4 lines): a hard-skipped stub —
  `it "skipped": expect(pending_reason.len()).to_be_greater_than(0)`.
- Baseline has an entry (`unit:lib/nogc_async_mut/mailbox_spec.spl`, line 771).
  No prior triage report covered this specific pair by name (only a
  same-day, different-topic bug doc,
  `stage2_mailbox_priorimailbox_rename_incomplete_blocks_build_2026-08-08.md`,
  mentions "mailbox" — that doc is about the Stage-2 build fix itself, not
  this spec file).
- **Action taken:** ported the canonical content into the shadow copy
  verbatim (restored reduced stub to match canonical) via the Edit tool.
- **New finding while verifying:** both the canonical and the now-restored
  shadow copy are RED — `bin/simple run` on either fails with
  `expected ... to contain class Mailbox:`, 1 example / 1 failure. Root
  cause: `stage2_mailbox_priorimailbox_rename_incomplete_blocks_build_2026-08-08.md`
  landed a legitimate rename of `mailbox_actor.spl`'s `class Mailbox` to
  `class PriorityMailbox` as part of its RESOLVED fix, but this spec's
  assertion (`actor_source.to_contain("class Mailbox:")`) was never updated
  to match the new class name. This is a genuine, pre-existing defect in the
  **canonical** spec, not something introduced by this session and not in
  scope to silently patch by weakening the assertion (per
  `.claude/rules/testing.md`: "a correct spec that fails is a legitimate
  artifact... leave it RED, file a bug"). Left both copies RED and matching;
  filing as a follow-up: the `to_contain("class Mailbox:")` assertion on line
  18/19 of both files should be updated to `to_contain("class PriorityMailbox:")`
  (or equivalent) by whoever owns the actor_scheduler rename follow-through.

### 2. `math_comprehensive_spec.spl` (`test/01_unit/lib/common/` vs `test/unit/lib/common/`)

- `diff -q` confirms the two files are byte-identical. **Already resolved**
  by a prior session — no action taken, no residual divergence.

## Part B — sample 5 (`NR%65==5`, 16 pairs)

All 16 pairs sampled at this residue were genuine drift (0 cosmetic-only,
0 "leave as legitimate divergence"). All were category-(a) reduced/stale
shadow stubs; canonical content was ported into the shadow copy for every
pair and re-run to confirm the mirrors now behave identically (not
necessarily green — two pairs surfaced pre-existing genuine failures that
match the canonical failure exactly, which is the correct aligned state).

| Pair | Canonical lines | Shadow (before) | Classification | Result after fix |
|---|---|---|---|---|
| `integration/app/gen_lean_log_modes_spec.spl` | 39 | 40 | stale shadow used raw `extern fn rt_process_run`; canonical uses modern `std.io_runtime.{process_run}` wrapper (verified `process_run` exists in `io_runtime.spl:170`) | 5/5 GREEN |
| `unit/app/interpreter/core/environment_spec.spl` | 320 | 320 | shadow had **tautology-guarded** assertions (`expect(true).to_equal(true)` / `expect(false).to_equal(true)`) replacing real `scope.bindings.len()` checks and `fail(...)` calls — matches the known "tautology-guarded false-green" family | 16/16 GREEN |
| `unit/app/ui/widget_table_list_upgrade_spec.spl` | 234 | 234 | shadow imported `app.ui.render.widgets` instead of `app.ui.render.html_widgets`; verified `render_html_widget` is only defined in `html_widgets.spl`, not `widgets.spl` | 33/33 GREEN |
| `unit/app/spl_coverage_spec.spl` | 48 | 4 | shadow was a near-empty stub | 3/3 GREEN |
| `unit/compiler/common/export_attr_spec.spl` | 174 | 174 | shadow used non-standard `from lexer import {Span}` (unresolvable module `lexer`); canonical uses `use compiler.frontend.lexer_types.{Span}` | mirrors aligned; **both now fail 6/9** on a genuine pre-existing bug — see "New finding" below |
| `unit/compiler/di/di_lock_spec.spl` | 246 | 203 | shadow missing the prevention-mock adoption block (U5, `sspec_prevention_mock_plan_2026-08-07.md`) | 15/15 GREEN |
| `unit/compiler/semantics/gc_boundary_check_spec.spl` | 168 | 84 | shadow missing `resolve_gc_alias` import/tests and had an inverted assertion (`does not warn` vs canonical's `warns...(symmetric rule)`) | 17/17 GREEN |
| `unit/lib/common/crypto/lshr_debug_spec.spl` | 29 | 24 | shadow had the OLD buggy `(x & -1) >> n` logical-shift implementation (arithmetic shift, wrong for negative inputs); canonical has the fixed `mask = (1 << (64-n)) - 1` version with an explanatory comment | 4/4 GREEN |
| `unit/lib/common/pure/nn/conv_spec.spl` | 19 | 4 | shadow was a near-empty stub | 2/2 GREEN |
| `unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl` | 273 | 273 | same tautology-guarded pattern as environment_spec.spl (`expect(false).to_equal(true)` instead of `fail(...)`, `expect(true).to_equal(true)` instead of a real message check) | 11/11 GREEN |
| `unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.spl` | 42 | 42 | shadow used stale field name `RingSlot(gen: 2, ...)`; canonical/actual struct field is `slot_gen` (`checkpoint_ring.spl:16`) | 2/2 GREEN |
| `unit/lib/nogc_async_mut/promise_spec.spl` | 246 | 226 | shadow missing the module-level `_promise_new_state` registry explanatory block and related plumbing | mirrors aligned; **both now fail 1/19** ("executor receives both callbacks" — pre-existing genuine failure, not introduced here) |
| `unit/os/compositor/hosted_backend_cocoa_spec.spl` | 63 | 60 | shadow missing a comment block + one assertion tied to the `is_macos()` runtime-probe fix (previously hardcoded `true`) | 7/7 GREEN |
| `unit/os/qemu_runner_tool_validator_spec.spl` | 196 | 196 | shadow used stale path `scripts/make_os_disk.shs`; actual file is at `scripts/os/make_os_disk.shs` (verified via `find`) | mirrors aligned; neither canonical nor shadow prints a `SPEC FILE VERDICT` line — pre-existing harness/`use`-warning issue (unresolved `os.qemu_runner` re-exports), unrelated to the path fix, present in canonical too |
| `unit/tools/ls_spec.spl` | 63 | 63 | shadow used raw `extern fn rt_file_exists`; canonical uses `std.io_runtime.{file_exists}` (verified exists in `io_runtime.spl:125`) | 6/6 GREEN |
| `rendering/backend_screenshot_compare_spec.spl` | 151 | 146 | **sampled but not fixed this pass** — larger diff (5-line delta across a 150-line rendering spec), deferred; flagging for a future sample rather than rushing a screenshot-comparison spec | left as-is, documented only |

### New finding: `export_attr_spec.spl` genuine pre-existing bug

Both canonical and (now-aligned) shadow fail 6/9 examples with
`semantic: class 'Span' has no field named 'end_pos'`. There are two
distinct `Span` structs in the compiler tree: `src/compiler/00.common/diagnostics/span.spl`
(`start, end, line, col, file, length`) and
`src/compiler/10.frontend/core/lexer_types.spl` (`start, end_pos, line, col`).
The spec imports `compiler.frontend.lexer_types.{Span}` (the `end_pos`
variant) but the resolved struct at test time appears to be the diagnostics
variant. This is a real name-collision/resolution defect, left RED and
un-modified per testing rules — not something to paper over by editing the
assertion.

## Files edited (Edit tool only, no destructive git ops)

- `test/unit/lib/nogc_async_mut/mailbox_spec.spl`
- `test/integration/app/gen_lean_log_modes_spec.spl`
- `test/unit/app/interpreter/core/environment_spec.spl`
- `test/unit/app/ui/widget_table_list_upgrade_spec.spl`
- `test/unit/app/spl_coverage_spec.spl`
- `test/unit/compiler/common/export_attr_spec.spl`
- `test/unit/compiler/di/di_lock_spec.spl`
- `test/unit/compiler/semantics/gc_boundary_check_spec.spl`
- `test/unit/lib/common/crypto/lshr_debug_spec.spl`
- `test/unit/lib/common/pure/nn/conv_spec.spl`
- `test/unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl`
- `test/unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.spl`
- `test/unit/lib/nogc_async_mut/promise_spec.spl`
- `test/unit/os/compositor/hosted_backend_cocoa_spec.spl`
- `test/unit/os/qemu_runner_tool_validator_spec.spl`
- `test/unit/tools/ls_spec.spl`

Not committed/pushed — left for the user to review and land via git plumbing,
per instructions.
