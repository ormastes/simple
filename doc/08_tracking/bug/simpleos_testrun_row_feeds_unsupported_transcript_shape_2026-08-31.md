# SimpleOS in-guest `testrun` row is red on every arch because the FIXTURE feeds a shape `parse_test_output` does not support

Date: 2026-08-31
Rows: `testrun` on both
`scripts/check/check-simpleos-x86-64-components-in-guest-ovmf.shs` and
`scripts/check/check-simpleos-aarch64-components-in-guest-efi.shs`
Entries: `examples/09_embedded/simple_os/arch/{x86_64,aarch64}/testrunner_component_entry.spl`
Product code: `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:304`

## The in-guest answer is CORRECT. The assertion is wrong.

Both arches print, byte-identically:

    [testrun] feeding a 3-example spec transcript to the real parser
    [testrun] FAIL parser did not report passed=2
    [testrun] FAIL parser did not report failed=1

This was previously read as an in-guest text defect (Defect 2 of
`simpleos_aarch64_in_guest_text_defects_not_len_abi_2026-08-31.md`). It is not.

**Measured on the HOST**, with the fully-working hosted runtime and the RUST
SEED (`simple run`), calling the same real `parse_test_output` on the exact
transcript the component entry builds:

    passed=0 failed=0 skipped=0 pending=0

and on the parser's own canonical summary shape:

    "Results: 3 total, 2 passed, 1 failed\n"  ->  passed=2 failed=1 skipped=0 pending=0

So the parser is healthy, and the guest is reproducing the host answer exactly.
The row asserts `passed == 2 and failed == 1` about an input for which the
correct answer is `0, 0` on every platform, hosted included.

## Why

The fixture is a **cargo-style** transcript ending in

    test result: FAILED. 2 passed; 1 failed; 0 ignored

`parse_test_output` has no `test result:` branch at all — the only summary form
it recognises is the canonical `Results:` line
(`test_executor_parsing.spl:336`), gated on `starts_with("Results:")` plus
`contains(" total")`, `contains(" passed")` and `contains(" failed")`.
`/usr/bin/grep -n 'test result:' src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`
returns nothing.

## Corroborating evidence that this is not an arch/runtime defect

* It is byte-identically red on x86_64 and aarch64, whose freestanding runtimes
  have *different* and independently-correct slice ABIs
  (`arch/x86_64/boot/rt_extras.c:1241` identity; aarch64 fixed in
  `simpleos_aarch64_rt_slice_misdecodes_raw_indices_2026-08-31.md`).
* Fixing the real aarch64 `rt_slice` tag-decode defect turned the caret row
  green and left this row unchanged.
* The x86_64 serial log shows the 4-tuple being built, set 4x and read 2x, so
  the tuple return path works; only the counts inside it are zero — which is the
  right answer for this input.

## What must NOT be done

Do not "fix" this by swapping the fixture to the `Results:` shape as a way of
turning the row green. Two legitimate resolutions, and choosing between them is
a product decision, not a gate decision:

1. **Teach `parse_test_output` the cargo `test result:` form.** This is real
   missing functionality if the runner is expected to consume cargo output;
   pick this if any caller actually feeds it that shape.
2. **Correct the fixture to a shape the runner supports**, and say so in the
   entry's own header — legitimate only if nothing feeds cargo output, i.e. the
   row was written against an imagined format.

Either way the row's discriminating power must survive: it has to fail if the
parser stops summarising correctly.

Until one is chosen, the `testrun` row is expected-red on both arches, and its
redness carries no information about in-guest execution.

## RESOLUTION 2026-08-31 — resolution 1 chosen: teach the parser the cargo form

Resolution 1 ("teach `parse_test_output` the cargo `test result:` form") was
picked over resolution 2, and the fixture was deliberately left byte-identical
on all three arches. The deciding evidence is that a *sibling product module*
already consumes exactly this shape:
`src/lib/nogc_sync_mut/test_runner/rust_test_runner.spl:60,69` parses
`"test result: ok. N passed; M failed; K ignored;"` with its own
`starts_with("test result:")` branch. So the runner IS expected to consume cargo
output; the shape was not imagined, and `parse_test_output` — the *general*
entry point the composite executor and the in-guest rows call — was simply
missing the branch its sibling already had. Swapping the fixture would have left
that hole open and made three gates green over it.

Implementation (`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`):
the cargo line is folded into the SAME "results family" the canonical
`Results:` line already forms — same segment reset, same `results_*` state, same
`results_pos` ordering — so all existing precedence rules (a later direct
`Passed:`/`Failed:` pair wins, a later BDD `N examples, M failures` wins, the
last summary of the file wins) apply unchanged to it with no new return path.
`ignored` maps to skipped; pending is 0. Recognition requires
`starts_with("test result:")` AND `contains(" passed")` AND `contains(" failed")`,
so authored prose such as `test result: inconclusive, see log` is not mistaken
for a summary — the same discrimination the canonical branch gets from its
` total`/` passed`/` failed` requirement.

### On failing loudly instead of returning zeros

Considered and deliberately NOT done in this change. `parse_test_output` returns
a bare `(i64, i64, i64, i64)`; there is no channel in that signature for "I did
not understand this transcript", and widening it ripples through
`make_result_from_output`, `test_executor_composite`, the outer runner, and all
three freestanding in-guest entries (which cannot format integers, let alone
carry an error type). The honest scope of this fix is that it removes *this*
instance of silent degradation rather than the class. The general remedy — a
recognised/unrecognised discriminant on the parse result, so "no tests ran" and
"unknown format" stop being the same answer — remains open and is the reason
this record stays filed rather than being closed outright.

### Regression cover

`test/01_unit/app/test_runner_output_parsing_spec.spl` gained five examples,
including the exact in-guest transcript. They were verified RED on the pre-fix
parser and GREEN after; the two precedence examples (cargo-then-canonical and
canonical-then-cargo) and the authored-prose example exist so the row keeps its
discriminating power rather than merely turning green.
