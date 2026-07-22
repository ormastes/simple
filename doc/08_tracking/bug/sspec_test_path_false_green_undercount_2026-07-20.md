# Bug: `simple test` false-green undercount (test-path miscompile)

Status: MITIGATED at defect site (char_code fix landed); BACKEND ROOT BUG OPEN
Observed: 2026-07-20 · Filed: 2026-07-21 · Root cause pinned: 2026-07-22
Severity: P0 — deploy blocker; invalidates `simple test` verdicts on the self-hosted binary

## Symptom
Self-hosted native binary only. `simple test <spec>` executes/reports a PREFIX of
the spec's declared `it` examples while claiming success:

- `test/01_unit/app/arch_check_spec.spl`: 74 declared → `Results: 18 total ...
  All tests passed!` with `--clean` (FALSE GREEN, exit 0); 66 warm.
- `test/01_unit/compiler/bitfield_sugar_spec.spl`: 28 declared → "no parseable
  pass/fail summary in test output; refusing synthetic pass" → 1 total, 1 failed
  (honest fail, different breakage of the same path).

`simple run <spec>` is correct on ALL backends (JIT / `--interpret` /
`--interpret-optimized`): 74/74 and 28/28. The defect is exclusively in the
`test` command path.

## Root cause (pinned 2026-07-22, disassembly-confirmed)
The native backend miscompiles `text` ordering comparisons (`<` `>` `<=` `>=`)
into **raw pointer/handle `cmp`** on the string handles. Chain of evidence:

1. `extract_number_before` / `extract_number_after_colon`
   (`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`) used
   `if ch < "0" or ch > "9"` on a one-char slice. Disassembly of the affected
   binary's compiled function shows a plain integer `cmp`+`jl`/`setg` on the
   `rt_slice`/`rt_string_new` return values — comparing heap ADDRESSES, not
   content. Result: digit detection returns address-dependent garbage, so
   `parse_test_output` silently drops whole result blocks → prefix undercount.
2. The MIR lowering DOES have content-aware guards
   (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` ~1432–1519:
   `rt_text_eq_any` for Eq/Ne, `rt_text_cmp_any` for Lt/Gt/LtEq/GtEq), but both
   are gated on `local_is_str()`, which keys off the MIR local type. In the
   full-CLI closure the MIR types of call/slice results degrade (not
   str-typed), the guard never fires, and lowering falls through to generic
   `emit_binop` = raw icmp. Proof: the affected binary contains NO
   `rt_text_eq_any` or `rt_text_cmp_any` symbol at all (only `rt_string_eq`,
   reached via stdlib method calls) — the guard fired zero times build-wide.
3. Address-dependence fully explains the previously mysterious
   "context-sensitivity": clean-vs-warm (18 vs 66) and minimal-closure-correct
   behavior are just different heap layouts flipping pointer comparisons.

Disproven earlier: test-runner logic bug, output-capture truncation,
parse-source bug, symbol collision, interpreter-backend abort. strace shows the
child emits all 74 result lines and the parent captures them all.
`--parallel`/`--fork` are separately broken (1/0 reported).

## Fix state
- **Defect-site fix LANDED**: digit checks in `test_executor_parsing.spl` now
  use `char_code()` + i64 compares (the lexer's proven-robust idiom;
  `src/compiler/10.frontend/core/lexer_chars.spl`). Semantics verified via
  probe on the affected binary (`run` path): all extraction cases correct.
  Full `simple test` re-verification requires a self-hosted rebuild (multi-hour
  parse wall) — in progress in the fix worktree.
- **Backend root bug OPEN**: `local_is_str()` type degradation in large
  closures means ~98 other `text` ordering-compare sites across the codebase
  remain miscompiled in full builds. Real fix = preserve str MIR types for
  call/slice results (or harden the guard). Until then, `text` `<`/`>` in code
  compiled into large native closures is UNRELIABLE — use `char_code()`.

## Arch coverage (2026-07-21)
- x86_64-unknown-linux-gnu: REPRODUCES (baseline above).
- i686 / armv7 / riscv32: full CLI is not a supported frontend target — filed as
  an honest gap, not claimed coverage.
- aarch64 / riscv64: fixture-level cross checks behaviorally identical to
  x86_64; full-CLI verification BLOCKED — cross-build lane broken independent
  of this bug (duplicate `parse_ce_decl` export [dedup in verification] +
  incomplete cross runtime bundles missing `rt_array_free` + self-hosted
  `native-build` SIGILL; see
  `doc/08_tracking/bug/cranelift_cross_arch_lane_broken_at_tip_2026-07-21.md`).

## Prevention (guard, NOT a substitute for the root fix)
`scripts/check/check-sspec-count-truthful.shs` — compares the STATIC declared
`it` count against the runner-REPORTED `Results: N total`. Fail-first validated:
fails arch_check (74≠18, FALSE-GREEN label) and bitfield (28≠1, MISMATCH label)
on the affected binary. Run per-arch via `SIMPLE_BIN=<binary-or-qemu-wrapper>`.
