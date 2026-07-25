# Implicit-self field ASSIGNMENT in `me` methods silently no-ops — while the linter recommends it

**Date:** 2026-07-17
**Status:** OPEN
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
