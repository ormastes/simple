# Implicit-self field ASSIGNMENT in `me` methods silently no-ops — while the linter recommends it

**Date:** 2026-07-17
**Status:** PARTIALLY FIXED (re-triaged 2026-08-08). The **interpreter lane is
FIXED** via fix direction 2 — a bare field assignment inside a `me` method is
now a hard semantic error with an on-point diagnostic, so the silent data loss
is gone there. The **seed JIT lane still silently no-ops** with no diagnostic.
Do not close until the JIT lane agrees. Evidence: "Re-triage 2026-08-08" below.
**Severity:** high (silent data-loss class; the tooling actively steers users into it)

## Symptom

Inside a `me` method, assigning to a field WITHOUT `self.` silently does
nothing:

```simple
class C:
    flag: bool
    me set_it():
        flag = true        # silently no-ops — self.flag stays false
    me set_it_explicit():
        self.flag = true   # works
```

Reproduced directly against the current bootstrap seed (opus review lane,
2026-07-17): implicit form leaves the field false; explicit form sets it.

## The compounding defect

The compiler prints "In Simple, 'self' is implicit in methods. Don't write
'self.'" and a lint hint recommending the implicit form — so following the
tool's own advice produces silently-broken mutation. (Field READS resolve
implicitly; ASSIGNMENTS bind a new local instead of the field.)

## Fix directions (either closes the trap)

1. Route implicit-name assignment inside methods to the field when the name
   matches a declared field (make assignment symmetric with reads), or
2. Make it a hard error / stop the lint recommending the implicit form for
   assignments specifically.

Filed per the CLAUDE.md rule: a short, safe form that fails must be fixed
or recorded, never silently worked around. Discovered as a landmine note by
the fix-guide selector lane; confirmed with a direct seed repro by the opus
review lane (see scratchpad fixguides/REVIEW.md of session 487db31f).

## Update 2026-07-18: reads fail hard too (struct+impl, not just class+me)

Reproduced with a `pub struct Foo: / impl Foo:` block (not `class`) on the
current `bin/simple` (Rust seed, per its WARNING banner) — worse than the
documented silent no-op:

```simple
pub struct Foo:
    x: i64
impl Foo:
    fn get_x() -> i64:
        x          # HARD semantic error, not silent no-op
```

Result: `error: semantic: variable `x` not found` / `HIR lowering error:
Unknown variable: x while lowering Foo.get_x` — a plain field READ, no
assignment involved. Confirmed by attempting the task-instructed "mechanical"
fix (drop `self.` in `src/lib/hardware/nand_emu/chip.spl`'s `data_out`,
`read_status`, `read_margin` methods): all became `variable not found` /
`function not found` and every `chip_spec.spl` example went red; reverted.
`.claude/memory/ref_coding.md`'s "Methods (implicit self)" section already
states the correct convention is `self.field in body` — "implicit self"
means omitting `self` from the parameter list, not omitting it from field
access. The lint hint (`error_recovery.rs:414-422`, fires unconditionally on
any `self.` token) is a parser-level false positive independent of whether
the surrounding construct even supports the implicit form it recommends.
`chip.spl` keeps its `self.` usages; removing them is not safe on this
binary.

## Update 2026-08-01: direction (2) chosen; guard landed, hint corrected

**Direction: (2) hard error.** Not (1). Reads are *not* symmetric today —
they already reject the implicit form (pure-Simple HIR: `unresolved name`;
pure-Simple interpreter `env_assign` miss → `undefined variable`; Rust seed
HIR: `UnknownVariable`). Making *assignment* resolve to the field while reads
keep erroring would create a new, worse asymmetry, and it contradicts
`.claude/memory/ref_coding.md`, where `self.field` in the body is the stated
convention. Erroring is also the narrower change: a bare `n = ...` may still
implicitly declare a local everywhere else — only the case where the name
collides with a field of the receiver is rejected.

State of each lane:

- Assignment guard for the Rust AST interpreter **already landed** in
  `941605d43d9` (`compiler/src/interpreter/node_exec.rs:581-597`), buried in a
  `chore: sync ...` commit. It is **not in the currently built seed**
  (`src/compiler_rust/target/bootstrap/simple`, built 2026-07-31 06:28 — the
  guard landed 2026-08-01 03:26), so a repro run today still shows the silent
  no-op. Re-verify after the next seed rebuild.
- The **compounding defect was still live** and is fixed here: the `JavaThis`
  recovery hint literally recommended `Simple:  x = value  # self is implicit`,
  i.e. the exact broken shape. Corrected in both trees to `self.x = value`
  (`src/compiler_rust/parser/src/error_recovery.rs`,
  `src/compiler/10.frontend/parser/recovery.spl`).
- The earlier claim that the hint "fires unconditionally on any `self.` token"
  is **stale**: `detect_common_mistake` gates `JavaThis` on the literal lexeme
  `this` (`error_recovery.rs:403-405`). Correct `self.` code is not flagged.

Regression spec:
`test/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.spl`
(4 of 5 failing before the hint fix, 5/5 after).

**Separate defect observed while reproducing (not fixed here):** under
`SIMPLE_EXECUTION_MODE=jit` an implicit field *read* returns `0` silently
instead of erroring, and a plain undeclared read/assign round-trip yields `0`
where the interpreter yields `7`. That is a JIT lenient-lowering divergence,
not this bug.

## Re-triage 2026-08-08 — interpreter FIXED, seed JIT still silently no-ops

Repro is this report's own `class C` with `me set_it()` (implicit `flag = true`)
and `me set_it_explicit()` (`self.flag = true`), constructed with
`C(flag: false)` and printed after the call.

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which
prints the Rust bootstrap-seed banner. No pure-Simple self-hosted binary is
deployed on this host, so both lanes below are seed lanes and the self-hosted
lane is untested.

**Interpreter** (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`) — FIXED:

    error: semantic: invalid assignment: `flag` is a field of `C`; a bare
    `flag = ...` creates a new local and leaves `self.flag` unchanged

That is fix direction 2 from this report, and the message names the field, the
class, and the exact consequence. The silent-data-loss failure mode is gone on
this lane, and it is the lane `bin/simple test` runs on.

**Seed JIT** (`bin/simple run`, the default for ordinary programs) — STILL
BROKEN, unchanged from the original report:

    implicit -> false
    explicit -> true

No error, no warning. The implicit assignment is still silently discarded.

So the defect now has the shape of an engine divergence rather than a universal
silent no-op: the engine the spec suite exercises rejects the code, while the
engine ordinary `run` uses accepts it and loses the write. That is worse for
discovery than either lane alone, because a spec cannot catch what only the
JIT does — the same structural hazard catalogued in
`run_vs_test_harness_divergence_2026-07-28.md`.

**Remaining work to close:** make the seed JIT lowering raise the same semantic
error. Since the diagnostic already exists on the interpreter side, the durable
fix is to move the check into a front-end/semantic pass that runs before either
lowering, so both engines inherit it rather than each implementing it.
