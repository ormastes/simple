---
id: bootstrap_logging_diagnostics_2026-07-07
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
severity: high
discovered: 2026-07-07
related: src/app/cli/native_build_main.spl
related: src/compiler/50.mir/_MirLowering/bootstrap_globals.spl
related: src/compiler/50.mir/_MirLowering/function_lowering.spl
related: src/compiler_rust/compiler/src/interpreter_sffi.rs
---

# Bootstrap logging diagnostics

## Problem

The bootstrap/native-build loop needed repeated reruns because the first failure
often reported only the final interpreter error, for example:

```text
undefined field 'id': cannot access field on value of type 'nil'
```

That does not say which MIR/HIR function or phase produced the bad receiver.

## Done

- Rust seed: plain IO extern calls routed through `rt_interp_call` now dispatch
  to the interpreter extern table (`print`, `print_raw`, `eprint`,
  `eprint_raw`, `dprint`, `println`, `eprintln`).
- Rust seed: field-access diagnostics already use
  `SIMPLE_DEBUG_FIELD_ACCESS` / `SIMPLE_BOOTSTRAP_DIAG` and cache the env lookup
  with `OnceLock`; receiver and stack strings are built only when enabled.
- Pure Simple native-build parent: worker failures containing
  `undefined field 'id'` now print the rerun hint
  `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1`.
- Pure Simple MIR: free bootstrap MIR progress logs are gated behind the shared
  MIR trace flag instead of printing unconditionally.
- Pure Simple MIR: function lowering caches the trace flag per function/block
  path and guards parameter-symbol `.id` access.

## Remaining items

- Reproduce the next bootstrap failure with
  `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1` and keep the log under
  `build/native_probe/`.
- If the next failure is still a nil `.id`, fix the shared symbol-id extraction
  site rather than adding caller-specific guards.
- If logs still lack the failing function after the rerun, add one more
  env-gated phase marker at the shared lowering entry that loses context.

## Evidence

- `cargo test -p simple-compiler --lib interpreter_sffi::tests::interp_call_dispatches_plain_io_externs --manifest-path src/compiler_rust/Cargo.toml`
- `bin/simple test test/01_unit/app/cli_native_build_main_contract_spec.spl`
- Seed compile checks passed for:
  - `src/app/cli/native_build_main.spl`
  - `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`
  - `src/compiler/50.mir/_MirLowering/function_lowering.spl`

## Runtime verification (2026-07-17)

No single deterministic repro exists for this issue as documented. Source grep confirms the "Done" items are present at tip: `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1` rerun hint present at `src/app/cli/native_build_main.spl:213`, and `interp_call_dispatches_plain_io_externs` test exists at `interpreter_sffi.rs:837`. The "Remaining items" are open-ended and require a real failure to reproduce; status remains IN_PROGRESS.

## Re-verification 2026-08-17 (CLI-entrypoint lane) — "Done" items CONFIRMED at tip, "Remaining" BLOCKED

Classified by CONTENT of current source, not commit ancestry. A full bootstrap
was forbidden this session (a live bootstrap owned the host at ~98% CPU), so the
three "Remaining items" — all of which require an actual bootstrap failure to
observe — were deliberately not attempted.

**Confirmed present in `src/app/cli/native_build_main.spl` (line numbers refreshed;
the older note's `:213` is stale, the file has since grown):**

- `native_build_output_has_nil_field_id` (line 238-239) matches
  `undefined field 'id'` on **both** stdout and stderr.
- `native_build_print_failure_hints` (241-244) prints the rerun hint
  `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1`, and is invoked on **both**
  failure paths in `run_native_build_worker`: the exit-0-with-no-output-binary
  path (277) and the non-zero-exit path (283).
- Diagnostic preservation across truncation (a genuinely new capability beyond
  the original "Done" list): `native_build_line_is_diagnostic` (186-197) +
  `native_build_collect_diagnostics` (199-205) re-emit every diagnostic line from
  the FULL stderr stream before `eprint_bounded` (207-236) head+tail truncates,
  so a `grep -c` over the relayed output can no longer report 0 for a diagnostic
  that actually fired.
- The worker's output is now relayed live (`process_run_timeout_live`, 267), so
  a slow-but-progressing worker is no longer indistinguishable from a hang.

Pinned as a source contract so these cannot silently regress:
`test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl`
(examples "keeps the rerun-diagnostics hint reachable from a failing worker" and
"preserves diagnostics across stderr truncation").

**Verdict: the entrypoint half of this bug is already fixed.** What keeps it open
is the open-ended follow-up work, which is not in these files.

### What could NOT be proven this session
- Whether the next real bootstrap failure still surfaces as a bare nil `.id`.
  Requires running a bootstrap — forbidden.
- Whether the shared symbol-id extraction site needs the root fix (item 2). That
  site is in `src/compiler/50.mir/_MirLowering/**`, owned by another lane.
- Whether an additional env-gated phase marker is still needed at the shared
  lowering entry (item 3) — same out-of-scope path.
- The Rust-seed evidence line
  (`interp_call_dispatches_plain_io_externs` in `interpreter_sffi.rs`) was not
  re-run; `cargo` builds were out of budget with the bootstrap holding the host.
