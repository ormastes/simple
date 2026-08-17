# `.?` evaluates to the payload, not a bool — 158 compiler-suite examples red

- **ID:** `exists_operator_returns_payload_not_bool_2026-08-04`
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Found:** 2026-08-04
- **Severity:** high (158 failing examples across
  `test/01_unit/compiler_core/branch_coverage_*_spec.spl` and
  `test/unit/compiler/coverage/branch_coverage_*_spec.spl`)

## Symptom

```
# scratch.spl
fn main():
    val opt = Some(42)
    print "exists={opt.?}"
    val d = {"key": "value"}
    print "dictexists={d.get("key").?}"
    val n: i64? = nil
    print "nilexists={n.?}"
```

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run scratch.spl
exists=42
dictexists=value
nilexists=nil

$ bin/simple run scratch.spl          # JIT lane — identical
exists=42
dictexists=value
nilexists=nil
```

Expected (what the specs assert): `true`, `true`, `false`.
Actual: the unwrapped payload, or `nil` when absent. Both engines agree, so
this is not an engine-divergence bug — it is the contract itself.

The suite hits it through a one-line helper repeated in every
`branch_coverage_*_spec.spl`:

```
fn check(condition: bool):
    expect(condition).to_equal(true)
...
    it "option is some":
        val opt = Some(42)
        check(opt.?)                  # -> expected 42 to equal true
    it "dict get - exists":
        val d = {"key": "value"}
        check(d.get("key").?)         # -> expected value to equal true
```

Failure-message census over the 2,471-file compiler scope (2026-08-04):
`expected 42 to equal true` ×59, `expected 10 to equal true` ×51,
`expected value to equal true` ×48 — 158 examples, all this one shape.

Note the second half of the defect: `check` declares `condition: bool` and is
handed an `i64`/`text` without any type error, so the mismatch only surfaces as
a matcher failure deep inside the example. That half is filed separately by a
parallel lane — the seed's `coerce_param` (`src/compiler_rust/.../arg_binding.rs:84`)
has no `bool` arm, so a `T?` bound to a `bool` parameter is neither
presence-coerced nor rejected; it is reported there as ~1,200 system-tier
failures whose common shape is `verify(x.?)`. This report covers the other half:
what `.?` itself yields. Fixing either one alone changes the outcome here, so
they should be decided together.

## Additional observed arm: array/pointer payload (`[u8]?`)

Added 2026-08-04 by the OS-suite lane. Same defect, third payload shape — the
payload is an **array**, so the leaked value prints as a whole buffer:

```
# test/01_unit/lib/alloc/mimalloc_spec.spl:245 "deallocate does not crash for valid ptr"
val alloc = MimallocAllocator(initialized: true)
val ptr = alloc.allocate(32, 8)      # -> [u8]?
val got_ptr = ptr.?
expect(got_ptr).to_equal(true)
```

```
✗ deallocate does not crash for valid ptr
    expected [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] to equal true
```

This one is a `val`-binding site (`val got_ptr = ptr.?`), which the report
below already names as off the `is_condition_present` allow-list — so it is
the same root cause, not a new one. Recorded because the shape matters for
triage: with an `i64`/`text` payload the failure message reads like a wrong
*value* (`expected 42 to equal true`) and is easy to misread as an assertion
bug, whereas the array form makes the leak unmistakable. Any fix under
option 1 must cover non-scalar payloads too.

Note this example was **masked** until 2026-08-04: `MimallocAllocator` was an
unresolvable dangling re-export from `src/lib/*/mimalloc.spl`, so the example
died at symbol resolution before reaching `.?`. Fixing that export
(`mimalloc.spl:56`, all three tiers) revived it and exposed this arm — i.e.
the count of `.?` victims is a floor, not a total; more are hidden behind
other resolution failures.

## Root cause

`Expr::ExistsCheck` is implemented as "unwrap the Option/Result layer; yield the
payload if present, `Value::Nil` if absent" —
`src/compiler_rust/compiler/src/interpreter/expr.rs:503-535`. That is
deliberate, and the surrounding comment says so. Because the result is a value
rather than a bool, every *condition* site needs a second, separate rule:
`is_condition_present` (`src/compiler_rust/compiler/src/interpreter_control.rs:165-180`
for if/elif/while/match-guards, and a duplicate at
`src/compiler_rust/compiler/src/interpreter_helpers_option_result.rs:19-24` for
`Option.filter` lambdas) special-cases `Expr::ExistsCheck` to mean "not Nil"
instead of running the payload through `Value::truthy()`.

So `.?` is only bool-like where a hand-maintained list of call sites says it is.
Passing `x.?` as a function argument, storing it in a `val`, or handing it to
`expect(...)` — none of which are on that list — all leak the payload.

This contradicts the language rule in `CLAUDE.md` /
`.claude/rules/language.md` ("`?` is operator only … Use `.?` over `is_*`
predicates"), which reads `.?` as a predicate, and it is the contract all 158
examples were written against.

## Why not fixed now

Two incompatible readings of `.?` are both load-bearing, and picking one is a
language decision, not a test fix:

1. Make `.?` yield `Bool`. Correct per the predicate reading and fixes all 158
   examples, but it invalidates every `if val x = y.?`-style site that currently
   relies on the payload flowing through, and the `is_condition_present`
   special cases would have to be deleted in the same change.
2. Keep the payload semantics and rewrite the specs to `check(x.? != nil)`.
   That silently changes what 158 assertions test and would have to be agreed
   as the contract first.

Either way the implementation lives only in the Rust seed
(`grep -rn "ExistsCheck" src/compiler/` finds nothing — the pure-Simple
compiler has no lowering for it yet), and the deployed `bin/simple` is that
seed, so no `.spl`-side change can move this. Needs an owner decision on the
operator's contract before any code moves.

---

# CORRECTION 2026-08-04 (later the same day) — MISFILED: this is not a defect

`.?` returning the payload is **correct by specification**, not a bug.
`doc/07_guide/quick_reference/syntax_quick_reference.md` states it explicitly:

> ### Existence Check (`.?`) — Returns `T?`
> The `.?` operator checks if a value is **present** (not nil AND not empty).
> It returns `T?` — the value itself if present, `nil` if absent. This enables
> pattern binding with `if val`.

Returning a bare `bool` would break `if val x = y.?` binding and `??`, both of
which need the value through. The implementation matches the contract:
`Expr::ExistsCheck` (`interpreter/expr.rs:503`) unwraps Some/Ok, decides
presence (nil, and empty array/dict/str count as absent), and yields the payload
or `Value::Nil`.

**The real defect** was one layer down: nothing coerced or rejected that payload
when it landed on a `bool` parameter, so `verify(x.?)` bound e.g.
`Value::Int(42)` into `condition: bool`. Fixed at the parameter boundary — see
`optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`,
which also carries the before/after table and a correction to the failure-count
attribution shared by this report.

**Status: CLOSED — not a defect.** Do not "fix" `.?` to return a bool.
Cross-references from sibling reports citing this file as the root cause should
be repointed at the parameter-binding report above.
