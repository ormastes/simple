# `only-compiled` is a dead tag; a `tag:` named argument silently DELETES the describe body

**Status:** OPEN — root-caused with an empirical fixture; fix NOT applied (see "Why unfixed").
**Filed:** 2026-08-10
**Found by:** Q31, from `doc/08_tracking/bug/app_mcp_intensive_spec_is_84s_not_a_hang_eight_real_failures_2026-08-10.md`
**Runnable check:** `sh scripts/check/check-bdd-tagged-block-drop.shs`
(negative control: `--expect-fail`).

## The skipping is not a feature. It is an argument-indexing bug.

The original observation was that `app_mcp_intensive_spec` tags 6 of 7 `describe`
blocks `only-compiled` and executes 5 of 35 examples. That reads as "a tag is
filtering examples". It is not.

**`only-compiled` has no implementation anywhere.** `/usr/bin/grep -rn
'only-compiled' src/` returns **zero** hits for the literal tag across every
language, including the whole Rust seed. (13 hits for the phrase *"only
compiled"* with a space exist; all are unrelated prose and 10 are vendored.)
Positive control: `slow_it` greps to 33 files over the same trees. There is no
tag parser, no tag filter, and no lane check. `only-compiled` was already
recorded as a dead tag in
`doc/08_tracking/bug/only_compiled_dead_tag_sweep_2026-07-03.md`.

What actually happens is positional:

- `src/compiler_rust/compiler/src/interpreter_call/bdd.rs` — `describe`/`context`
  take the body as `eval_arg(args, 1, ...)`, a **hard-coded index 1**.
- `src/compiler_rust/compiler/src/interpreter_call/core/arg_eval.rs:33` —
  `eval_arg` is purely positional and never inspects `arg.name` / `arg.label`.
- So in `describe "x", tag: ["only-compiled"]:` the tag array sits at index 1 and
  the real body at index 2. **The tag array is evaluated as the block.**
- `exec_block_value`'s fallthrough arm is `_ => Ok(Value::Nil)`. A non-block
  silently becomes Nil. The body never executes, nothing is raised, nothing is
  recorded.

`it` has the same hard-coded `block_index = 1`, and there the outcome is worse:
the example is still registered and counted, with a Nil body — a **tautology
green**, not even a skip. Only `limited_it` does the named-argument lookup
correctly, by explicitly taking `args.len() - 1`.

## Measured proof

Fixture (`scripts/check/check-bdd-tagged-block-drop.shs` generates it): four
declared examples, two in an untagged `describe`, two under a `tag:` argument.

```
2 examples, 1 failure      <- untagged group ran
0 examples, 0 failures     <- tagged group: body never executed
SPEC FILE VERDICT: ... declared>=2 executed=2 passed=1 failed=1 dropped=0
```

Four examples were declared. The verdict line reports `declared>=2 executed=2`
and — the part that makes this a false green rather than an honest skip —
**`dropped=0`**. The two vanished examples are absent from every number, and the
runner positively asserts that nothing was dropped. This is the same shape as
`reason=zero-examples`: a healthy-looking verdict line over a spec that did not
run.

A `dropped=` field already exists in the verdict line, so surfacing this needs a
counter, not a new format.

## Corpus census

`/usr/bin/grep` over `test/`, xargs-based, every zero positive-controlled.

| leg | files with `only-compiled` | tagged blocks | examples silently dropped |
|---|---|---|---|
| `test/01_unit` | 42 | 48 | 67 |
| `test/unit` | 32 | 33 | 33 |
| `test/02_integration` | 11 | 11 | 0 |
| `test/integration` | 16 | 34 | 31 |
| `test/03_system` | 14 | 65 | 138 |
| **all `test/` (both legs execute)** | **146** | **279** | **443** |
| de-duplicated across duplicate legs | ~115 | — | **~376** |

Of the 279 tag occurrences: 204 on `describe`/`context` (these delete their
bodies), 3 on `it` (these become tautology greens), 72 in inert `# @tag:`
comments.

**~376 to 443 examples are silently absent from the corpus** while every spec
containing them reports a healthy verdict.

## `slow_it` — the "pass-through" claim is REFUTED

The predecessor recorded `slow_it` as "a pass-through that gates nothing". At the
BDD level that is true — `bdd.rs` matches `"it" | "slow_it" | "limited_it"` with
identical execution semantics. But it is **not** unused, so the repo rule
"implement or delete" does not apply: it gates a real timeout.

- `src/app/test_runner_new/test_runner_single.spl:837` raises the per-spec
  timeout to a 600s floor when the file contains `slow_it `.
- Mirrored at `src/app/test_runner_new/test_runner_client.spl:321`.
- Also consumed by `test_manifest_scanner.spl:163` (`slow_tag:`),
  docgen `generator.spl:156`, lint `traceability_and_assertions.spl:349`.

Corpus usage: 3,118 files, 44,089 call sites — the dominant example keyword.
**Do not delete `slow_it`.**

## Fix

Two parts; the second is worthless without the first.

1. **Select the block as the trailing positional argument**, not index 1, for
   `describe`/`context`/`it`/`slow_it` — generalising what `limited_it` already
   does. Concretely, a helper that scans `args` in reverse for the last argument
   with `arg.name.is_none() && arg.label.is_none()`, returning that index if
   `>= 1` and otherwise falling back to `1` (so a description-only call keeps
   relying on `eval_arg`'s out-of-range Nil default).
2. **Close the fail-open in `exec_block_value`.** Split the `_ => Ok(Value::Nil)`
   fallthrough into `Value::Nil => Ok(Value::Nil)` (a pending `it` with no body
   is legal) and `other => Err(CompileError::semantic(...))` naming the received
   type. Silently returning Nil for a non-block is what hid 443 examples; it must
   be loud.

Expected consequence, and it is the correct one: ~376-443 previously invisible
examples begin executing, and some will be RED. Per repo rule they stay RED and
get filed — they must not be re-hidden behind the tag.

Once fixed, `only-compiled` should be deleted from all 146 files (it has never
meant anything) or given a real implementation. Do not leave a tag that reads as
a filter but is not one.

## Why unfixed in this change

`src/compiler_rust/compiler/src/interpreter_call/bdd.rs` is **actively contested**.
A concurrent session landed `47ba20fda2b fix(spec-dsl): fail vacuous expect()...`
in it and is still mid-flight: this fix was applied to the working copy and was
**clobbered back to HEAD within minutes**, before it could be compiled. Per
`.claude/rules` ("don't touch a file another concurrent session is mid-flight
on"), it is left for the owning session rather than raced. The patch shape above
is complete and the check below proves whether it worked.

## Unblock condition

`sh scripts/check/check-bdd-tagged-block-drop.shs` exits 0 with
`PASS -- all 4 declared example(s) accounted for`, and `--expect-fail` then
correctly FAILs. Then re-run the census: the 443 figure must go to 0.
