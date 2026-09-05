# Feature: `bin/simple run` vs `bin/simple test` harness divergence — measurement

## Raw Request
Measure how wide the newly-discovered harness split is: `bin/simple run` and
`bin/simple test` give different answers for the same expression on the same
binary (`[i64].index_of(10)` -> `<value:0xffffffffffffffff>` under `run`, `0`
under `test`). Measurement task, not a fix task.

## Task Type
measurement / bug-triage

## Status
**COMPLETE (measurement).** No product code changed. Deliverable landed at
`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`.

## What was measured
60 single-method differential probes across array, dict and text receivers,
each its own program with a byte-identical evaluation body, run through both
harnesses on the same binary (`bin/release/x86_64-unknown-linux-gnu/simple`,
built 2026-07-27 22:06, the Rust bootstrap seed).

Result: **31 AGREE / 18 DISAGREE / 11 UNMEASURED-on-JIT** (all 11 dict probes).
Per receiver — array 14 DISAGREE of 27; text 4 of 22; dict 0 measurable of 11.
The `test`/interpreter answer is the correct one in every DISAGREE row.

## Root finding
The split is **engine**, not harness plumbing:

- `bin/simple run` -> Cranelift **JIT** by default (`driver/src/exec_core.rs:629`)
- `bin/simple test` -> tree-walk **interpreter**, hard default
  (`driver/src/cli/test_runner/types.rs:292`)
- `TestExecutionMode` has four variants — `Interpreter`, `Smf`, `Native`,
  `Composite` — and **no JIT variant** (`types.rs:57-67`). The engine ordinary
  programs run on is structurally unreachable from the spec suite.

Four parallel hand-synced JIT method->`rt_*` dispatch tables (`codegen/instr/calls.rs`,
`codegen/instr/methods.rs`, `codegen/instr/closures_structs.rs`,
`codegen/llvm/functions.rs`) versus one interpreter table
(`compiler/src/interpreter_method/`) is the structural cause.

## Landmines recorded
- `SIMPLE_NO_JIT=1` is a **NO-OP** on `bin/simple`. It is read only by the
  pure-Simple interpreter (`src/compiler/10.frontend/core/interpreter/mod.spl:194`)
  and by nothing in `src/compiler_rust/`. The working knob is
  `SIMPLE_EXECUTION_MODE=interpreter|jit`.
- **Whole-program silent engine demotion.** Any JIT failure anywhere in a module
  (e.g. one unresolved `rt_dict_insert` from a single `d.insert(...)`) demotes
  the ENTIRE program to the interpreter with only a stderr `[INFO]` line. The
  first version of this probe reported 38/38 AGREE for exactly this reason. Any
  differential probe MUST be one method per program.
- Demotion also triggers on **source text**: a file containing `get_cli_args`,
  `rt_cli_get_args`, `std.cli`, or `window_winit` is auto-interpreted
  (`exec_core.rs:881-901`). Adding an unrelated import changes the engine.
- JIT fails **open**: `Runtime error: Function 'Array.map' not found` on stderr,
  **exit 0**, garbage value returned. `text.to_upper` is a silent no-op with no
  diagnostic at all.
- Wrong answers present as a leaked tag box (`<value:0xffffffffffffffff>`) or a
  shifted int (`first`/`last`/`pop` return `v << 3`), never a clean sentinel.

## Stale-binary caveat
`src/compiler_rust/compiler/src/codegen/instr/calls.rs` (mtime 07-28 00:38) and
`runtime/src/value/collections.rs` (07-28 00:37) already contain the correct
receiver-polymorphic `rt_index_of` wiring, and both are `M` in git. The deployed
binary predates them (07-27 22:06). A rebuild is expected to close the six
`index_of` rows; the other 12 DISAGREE rows are separate defects.

## Artifacts
- `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md` — full table
- `build/probe_divergence/cases.txt` — 60 probe cases
- `build/probe_divergence/fast_driver.shs` — JIT vs interpreter (~3 min)
- `build/probe_divergence/probe_driver.shs` — real `run` vs real `test` (~90 min)
- `build/probe_divergence/fast_results.tsv`, `results.tsv`

## Measurement integrity
- **Both drivers completed all 60 cases and agree 60/60 on every value.** The
  engine-level substitution (`SIMPLE_EXECUTION_MODE`) and the real
  `bin/simple run` / `bin/simple test` pair give identical results. A naive
  string diff shows 15 rows differing only by the fast driver's extra
  `exit=139` / `<via-jit-bailout>` annotations; no semantic value differs.
- `probe_driver` records a spec with `0 examples` or with no `N examples` line
  as `<UNMEASURED>`, never as agreement. **0 of 60 hit either condition.**
- **Assertion calibration passed:** a deliberately-wrong spec
  (`expect(a.index_of(10)).to_equal(999)`) DID fail under `bin/simple test`
  (`expected 0 to equal 999`, 1 example / 1 failure, exit 1). The harness really
  executes `it` bodies and assertions. Note this contradicts the caveat in
  `.claude/rules/testing.md` that interpreter mode "only verifies file loading,
  NOT `it` block execution" — that caveat did not hold here and should be
  re-checked. Calibration spec deliberately NOT committed.

## Next (not done — measurement task)
1. Rebuild `bin/simple`, re-run `fast_driver.shs`, diff.
2. Add a JIT test-execution mode so specs can cover both engines.
3. Make the JIT dispatch table fail closed instead of exit-0-with-garbage.
4. Collapse the four parallel Rust dispatch tables into one.
5. Retire or wire up `SIMPLE_NO_JIT`.

## Re-measurement 2026-07-28 (item 1 above: DONE)
60-probe corpus re-run on freshly built `src/compiler_rust/target/debug/simple`
(mtime 2026-07-28 11:06:17): **51 AGREE / 9 DISAGREE / 0 UNMEASURED** (was
31/18/11). 0 silent JIT fallbacks. 12 probes fixed; 6 still divergent; **3 new
regressions** (`dict_get_or_present`, `dict_get_or_absent`,
`dict_insert_then_keys` — dict now JIT-compiles instead of bailing out, so `run`
went from correct-via-bailout to wrong-with-exit-0 on missing `Dict.get_or` /
`Dict.insert`). Dict is **no longer uncompilable** on the JIT (0/11 bail out),
superseding the original blanket finding. `arr_filter`/`arr_any`/`arr_all`
changed SIGSEGV → silent wrong value (same verdict, worse failure mode).
Item 3 (fail closed instead of exit-0-with-garbage) is now the highest-value
follow-up — it is the mechanism behind all 3 regressions. Full table + three
groups: `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`
§ "Re-measurement". `fast_driver.shs` gained a `PROBE_BIN` override; it had
hardcoded the stale deployed `bin/simple`.

## Re-measurement 2026-07-29 (measurement only, no fixes)
Same 60-probe corpus on a fresh `target/debug/simple` build (mtime 2026-07-29
02:55:53): **58 AGREE / 2 DISAGREE / 0 UNMEASURED**, of which 4 AGREE rows
(`arr_map`/`filter`/`any`/`all`) are AGREE-via-demotion (`8b72b34f005` lambda
guard — no `[jit-addr]`, JIT never ran), so AGREE-on-actual-JIT is 54. The 3
prior "regressions" are now 1: `dict_insert_then_keys` and `text_lines_len` and
`text_parse_int` are real fixes (confirmed `[jit-addr]`); `dict_get_or_present`
/`dict_get_or_absent` remain DISAGREE — `Dict.get_or` is still unrouted, same
symptom as before. **Zero new `AGREE→DISAGREE` regressions.** Full table:
`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`
§ "Re-measurement — 2026-07-29".
