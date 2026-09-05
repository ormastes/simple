# Implicit-self field ASSIGNMENT in `me` methods silently no-ops — while the linter recommends it

**Date:** 2026-07-17
**Status:** FIXED IN SOURCE 2026-08-08 — both lanes now hard-error. The JIT half
(the last open half) was closed by moving the check into HIR lowering, upstream
of every lowering-based engine. Guard:
`scripts/check/check-implicit-self-field-assignment.shs`. Pending the next seed
redeploy the guard is RED against the stale deployed `bin/simple` and GREEN
against a freshly built seed — see "Fix 2026-08-08" below.
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

## Fix 2026-08-08 — JIT lane closed in HIR lowering

Done exactly as the paragraph above prescribes: the check now lives in **HIR
lowering**, upstream of both the Cranelift JIT and the LLVM/native backends, so
every lowering-based engine inherits it instead of each re-implementing it. The
AST interpreter keeps its own guard (it does not go through HIR); the two
messages are deliberately worded in lockstep.

- `src/compiler_rust/compiler/src/hir/lower/error.rs` — new
  `LowerError::ImplicitSelfFieldAssignment { field, class }`.
- `src/compiler_rust/compiler/src/hir/lower/memory_check.rs` — new
  `check_implicit_self_field_assignment`.
- `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` — called from the
  `Node::Assignment` arm **before** `lower_expr(&assign.target)`. Order is
  load-bearing: lowering a bare unbound identifier in assignment position is
  precisely what mints the shadowing local, so a check placed afterwards would
  inspect the freshly-created local and see nothing wrong.

**The check is NOT gated on `lenient_types`, and that was the whole bug on this
lane.** The first revision copied the sibling `check_self_mutation_in_fn_method`
and skipped when `lenient_types` was set. It built clean and changed nothing:
the probe still printed `implicit -> false`. `pipeline/execution.rs:989` — the
`bin/simple run` / JIT lane — calls `set_lenient_types(true)`, so the guard had
self-disabled on exactly the engine that had the defect. `lenient_types` means
"unknown TYPES degrade to ANY"; it is a different question from "this name is a
declared field of a class we resolved concretely". Soundness here comes from the
concrete-class requirement, not from leniency.

Scoping, chosen so no working code breaks: only inside a method (`ctx.has_self`)
— implicit local declaration is untouched in free functions; only when the name
has no existing local/parameter binding — a local that shadows a field keeps
shadowing it and stays re-assignable; only when the receiver's class type is
**concrete**. `TypeId::ANY` is skipped deliberately, because `get_field_info`
falls back to a fuzzy whole-tree field search for ANY, which would let an
unrelated struct elsewhere in the repo turn an ordinary local into a hard error.

### Evidence, both directions

`scripts/check/check-implicit-self-field-assignment.shs`. It asserts three
things per engine, not just "exits non-zero": the implicit form is rejected, the
diagnostic **names the field** (an anonymous error is not an acceptable fix),
and — the sabotage sentinel — `self.flag = true` still compiles and still sets
the field, so a compiler that rejected all assignment cannot pass. It also fails
on the literal string `implicit -> false`, the exact silent-no-op signature.

    # RED — stale deployed bin/simple (pre-fix binary):
    FAIL — engine 'jit': implicit field assignment SILENTLY NO-OPPED — the
    program ran to completion and printed 'implicit -> false', so the write to
    `flag` was discarded with no diagnostic

    # GREEN — freshly built seed carrying the fix:
    SIMPLE_BIN=src/compiler_rust/target/release/simple sh \
      scripts/check/check-implicit-self-field-assignment.shs
    PASS — 2 engine setting(s) checked: interpreter,jit — implicit `field = ...`
    in a method is a hard error naming the field, and explicit `self.field = ...`
    still works

The RED run is against a real pre-fix binary, and the intermediate
`lenient_types`-gated revision is itself a third data point: it was a real build
of a real code change that the guard correctly refused to pass.

**Why a shell guard and not a `*_spec.spl`:** `bin/simple test` runs the AST
interpreter, which has rejected this shape since `941605d43d9`. The broken lane
was `bin/simple run` (JIT). No assertion writable in the spec DSL can observe
it — the suite cannot reach that engine. Same structural gap as
`run_vs_test_harness_divergence_2026-07-28.md`.

**Not yet closed:** `bin/release/<triple>/simple` still predates this fix, so
the guard is red until the next seed redeploy. The fix is in source and proven
on a built binary; redeploying the shared binary was out of scope for this lane.
