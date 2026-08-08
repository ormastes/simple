# Lane NILQ — nil / presence-testing defects

**Date:** 2026-07-27 · **Status:** characterized + contained · **Commits:** none (lane is no-commit)

## Verdict

Two reported defects resolved into one compiler defect plus one
never-existed-builtin.

### (a) `.?` is mis-lowered on the JIT — CONFIRMED, root-caused, filed

The spec (`doc/07_guide/quick_reference/syntax_quick_reference.md` L497-531) is
unambiguous: `.?` returns `T?` — present iff *not nil AND not empty*, with
"primitives always present". The gap is entirely in the JIT/native lowering.

**The two engines return different TYPES from the same operator:**

| expr | spec | JIT | interpreter |
|---|---|---|---|
| `(0).?` | `0` | `false` (**bool**) | `0` (**i64?**) |
| `(7).?` | `7` | `true` | `7` |
| `Some(0).?` | `0` | `false` | `0` |
| `Some(5).?` | `5` | `true` | `5` |
| `None.?` | `nil` | `false` | `nil` |
| `"".?` | `nil` | `true` | (nil) |
| `"xy".?` | `"xy"` | `true` | `"xy"` |
| `[].?` | `nil` | `true` | (nil) |
| `[1,2].?` | `[1,2]` | `true` | `[1,2]` |

Truthiness truth table: **JIT 5/13 wrong, interpreter 13/13 correct.**
The JIT emits a raw machine-word `!= 0` test: for an `i64` payload that
degenerates to a zero-test; for `text`/array the word is a never-null heap
pointer so the emptiness half of the spec is dropped entirely. Both error
directions fall out of that one mis-lowering.

**Fix belongs in `src/compiler/**` (JIT/native lowering of the existence-check
operator). NOT patched — lanes are live in that tree.** The interpreter needs
no change; it is the correctness oracle.

### (b) `is_nil` — NOT a dispatcher gap; it is not a builtin at all

Reported as "unresolvable on `Option::None` and struct values". Actually
unresolvable on **9 of 9 receivers on both engines** (i64, text, array, struct,
`Option<i64>` Some/None, `Option<struct>` Some/None). Every `fn is_nil` in the
tree is a method on a specific compiler/interpreter `Value` type; all 26
in-tree call sites are on those receivers. There is nothing to populate.
Residual defect: the interpreter rejects it at **compile time**, the JIT defers
to a **runtime** error — so a cold-path `.is_nil()` ships and detonates later.

## Reconciliation of the two source lanes

TOINT (".? false for Some(0); on the interpreter it isn't even a bool") and
SPECFIX ("`expect(xs.?)` is a no-op, `.?` yields the receiver") were observing
**the same defect from opposite engines** — TOINT the JIT column, SPECFIX the
interpreter column.

## What is SAFE (verified both engines) — the containment idioms

- **`== nil` / `!= nil` — 15/15 correct and mutually consistent**, including
  `Option<struct>`. This is what hazardous sites were migrated to.
- **`if val x = opt.?:` pattern binding — correct on both engines**, including
  `Some(0)` (binds, `x == 0`). The dominant real-world idiom is NOT affected;
  only the *bare-truthiness* form is broken. This sharply limits blast radius.
- `index_of` / `last_index_of` / `find` return a plain i64 with **-1** for
  not-found on both engines → guard with `< 0`.

Residual divergence: `Option<text>` holding `Some("")` — JIT treats present,
interpreter treats absent (both bare and binding forms). Spec is ambiguous
here; it needs tightening *and* the engines need to agree.

## Containment landed

23 hazardous sites repaired out of 347 bare-truthiness guards / 1,216 `.?`
lines in owned `src/**`. ~324 are benign (`Option<struct/handle>` receivers,
where the mis-lowering coincidentally agrees with the spec).

- Class A (14): plain-i64 `-1` sentinels → `< 0` — `ftp_utils.spl` ×2,
  `env/variables.spl` ×2.
- Class B (9): genuine `Option<i64>` with 0-valued payloads → `== nil`/`!= nil`
  — database `test_extended` ×4, `async_host/scheduler.spl` ×3,
  `worker_thread.spl`, `actor_scheduler.spl`.

Lint A/B'd against `HEAD` per file: error counts identical to baseline, **zero
new lint errors**.

## NOT done, deliberately

**1,954 `expect(X.?)` assertions** across `src/` and `test/` are not presence
assertions on either engine (vacuous on the interpreter; asserting truthiness —
constantly `true` for text/array receivers — on the JIT). Not bulk-rewritten:
that would make ~2k green assertions start asserting for the first time and
needs its own lane with per-file red/green review.

## Honest verification caveat

The end-to-end A/B of `expand_var` (working tree vs `HEAD`) showed **identical
correct output for both** — it did not reproduce a user-visible failure,
because that module fails JIT compilation here
(`higher_layer_runtime_family`) and falls back to the interpreter, where `.?`
is correct. The hazard is evidenced generically by the isolated truth table
instead. The repairs stand as engine-independence fixes. No PASS is claimed
that was not observed.

**The `simple test` runner never executed either spec.** The vacuity probe
(`build/nilq_probe/vacuous_spec.spl`) eventually **exited 0** — but its entire
901-byte output is lint warnings, with **zero** `"N examples, M failures"`
lines. Per the sspec contract (one such line per `describe` block), the absence
of any line means **no example ran at all**. So this is not a hang: it is a
**false green** — `simple test <file>` exits 0 having run nothing, which any CI
would read as PASS. That is a separate defect in its own right and is filed
below. The second run (the real spec) was still pending at lane close.

Consequence: the new spec is lint-clean but has **NOT** been executed by the
runner, and no PASS is claimed for it. Every one of its assertions was instead
verified individually via `bin/simple run` on both engines, which is why the
spec was written to assert only those independently-verified propositions.

### Additional defect observed: `simple test` exits 0 without running examples

`bin/simple test build/nilq_probe/vacuous_spec.spl` → exit 0, no examples
executed, no failure reported. A spec that cannot even be scheduled reports
success. This deserves its own lane; it means green `simple test` results are
not by themselves evidence that anything was verified. (Consistent with the
prior `sspec false-green` and `SMF-stub shadowing` findings in memory.)

## Artifacts

- Probes: `build/nilq_probe/tt_dotq.spl`, `tt_cmp.spl`, `tt_bind.spl`,
  `tt_value.spl`, `isnil_*.spl` (9), `idx2.spl`, `expand_ab.spl`
- Bugs: `doc/08_tracking/bug/dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27.md`,
  `doc/08_tracking/bug/is_nil_is_not_a_language_builtin_2026-07-27.md`,
  `doc/08_tracking/bug/dotq_zero_test_hazard_call_sites_2026-07-27.md`
- Spec: `test/01_unit/language/nil_presence_idioms_spec.spl`

## Binary identity

All results from `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`,
which **prints the Rust bootstrap-seed banner**. `build/native_probe/simple`
prints the same banner. No non-seed binary was available in this worktree;
findings are attributed to the seed and should be re-confirmed against a
self-hosted binary once redeployed. Engine columns were selected on the same
binary via `SIMPLE_EXECUTION_MODE=interpreter`.
