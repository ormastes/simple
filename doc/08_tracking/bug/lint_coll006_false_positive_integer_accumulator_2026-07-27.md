# COLL006 "string concat in loop" fires on plain integer accumulators (`i = i + 1`)

**Status:** fixed 2026-07-28 (working copy) — see .spipe/lint_coll006/state.md
**Found:** 2026-07-27 (KV260 JTAG-console completeness work)
**Area:** compiler/35.semantics/lint — `collection_patterns.spl`
**Severity:** medium — CRITICAL-severity false positive; makes `simple lint` red
across the whole hardware tree and fails the test-runner's post-spec lint gate

## Symptom

`COLL006 string concat in loop (O(n^2))` is reported for functions whose only
`x = x + y` statement is an **integer loop counter**:

```
src/lib/hardware/fpga_k26/test/jtag_console_spec.spl:28:0: error[COLL006]: string concat in loop (O(n^2))
  hint: use StringBuilder instead of str = str + x
```

Line 28 is `fn pack(bytes: [i64], buf_words: i64) -> [i64]`, whose loop body
contains `w = w + 1` and `i = i + 1` and no text at all.

## Control — this is not new code's fault

Untouched, silicon-proven sources fail identically:

```
$ bin/simple lint src/lib/hardware/fpga_k26/k26_xdc.spl \
                  src/lib/hardware/vhdl_gen/ctrl_obs_slave_gen.spl
src/lib/hardware/vhdl_gen/ctrl_obs_slave_gen.spl:178:0: error[COLL006]: string concat in loop (O(n^2))
src/lib/hardware/vhdl_gen/ctrl_obs_slave_gen.spl:254:0: error[COLL006]: string concat in loop (O(n^2))
Found 6 error(s), 2 warning(s)
```

## Cause

`src/compiler/35.semantics/lint/collection_patterns.spl:177` gates COLL006 on
`is_string_concat_assign_expr(e)`, which appears to mean "`x = x + <non-array>`"
— there is no type check that the accumulator is `text`. Every `i = i + 1` in a
loop matches. The diagnostic is also reported at the enclosing function's line
(`item_name: fn_name`) rather than the offending statement, which is why the
reported line points at a `fn` signature and makes the report hard to act on.

## Impact

1. `bin/simple lint` cannot be used as a gate on `src/lib/hardware/**` — the
   baseline is already red, so a genuine new COLL006 is invisible.
2. The test-runner's post-spec lint gate turns this into a phantom test
   failure: every example passes, then the file is reported FAILED. Observed on
   `jtag_console_spec.spl` (20 examples green → "21 total, 20 passed, 1
   failed") and reproduced on the untouched `xdc_gen_spec.spl` (15 green → "16
   total, 15 passed, 1 failed"). See
   `test_runner_post_spec_lint_gate_empty_file_arg_2026-07-20.md` for the gate
   itself.

## Fix

Require the accumulator's inferred type to be `text` before emitting COLL006
(integer/float accumulators are O(1) per step, not O(n^2)), and anchor the
diagnostic to the assignment's own line instead of the function's.

A regression case should cover: `text` accumulator in a loop → COLL006 fires;
`i64` accumulator in a loop → no diagnostic.
