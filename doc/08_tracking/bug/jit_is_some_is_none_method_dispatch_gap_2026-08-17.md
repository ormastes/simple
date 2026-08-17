# JIT: `.is_some()` / `.is_none()` method calls fail closed OR return a raw untagged bool

- **ID:** jit_is_some_is_none_method_dispatch_gap
- **Date:** 2026-08-17
- **Status:** OPEN (P1)
- **Severity:** high — one shape is a silent wrong result (`nil` where `true`
  belongs), the other is a hard stop. Both on the default `bin/simple run` lane.
- **Component:** seed JIT method dispatch,
  `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1904`
- **Lane:** Rust bootstrap seed, cranelift JIT. The tree-walk interpreter is
  CORRECT — this is a cross-engine divergence.

## How it was found

Not filed from a report. It surfaced as residual failures in the run-path probe
`test/01_unit/compiler/codegen/probe_option_presence_falsy_payload.spl`, written
for a *different* defect (the `rt_is_none` zero/nil bit-pattern collision, see
Cross-refs). Once that fix landed, 4 of the original 9 JIT failures survived —
and they behaved differently from the rest: **wrong for PRESENT and ABSENT
receivers alike**, which is what proves they are not a presence bug.

## Reproduction

Against a seed freshly built from `88227f48202` **plus** the `rt_is_none` fix
(so this is not that defect leaking through):

```simple
fn zero_i64() -> i64?:
    return 0

fn main() -> i64:
    val o: i64? = 0
    print(o.is_some())     # JIT: Runtime error: Function 'is_some' not found (exit 70)
    print("ab".contains("a"))   # JIT: true  <- CONTROL: bool boxing works generally
    return 0
```

Shape A — **fails closed** when the receiver is a plain local:

```
Runtime error: Function 'is_some' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not
a program error. Refusing to substitute a placeholder value (...)
exit 70
```

Shape B — **silently wrong** when the receiver is a function-call result
(`zero_i64().is_some()`), as measured by the probe before these rows were
removed from it:

| expression | JIT | interpreter (correct) |
|---|---|---|
| `zero_i64().is_some()` | `nil` | `true` |
| `zero_i64().is_none()` | `0` | `false` |
| `absent_i64().is_some()` | `0` | `false` |
| `absent_i64().is_none()` | `nil` | `true` |

## Root cause

`closures_structs.rs:1904` lowers the call correctly — it invokes `rt_is_some`
and the runtime helper returns the right answer — but then does:

```rust
let bool_result = builder.inst_results(call)[0];
let result = builder.ins().sextend(types::I64, bool_result);
return Ok(Some(result));
```

That yields a **raw** `0`/`1`, not a tagged `RuntimeValue`. Runtime tags live in
the low 3 bits, so a raw `1` is `0b001` = `TAG_HEAP` and renders as `nil`
(or as an invalid heap reference), while a raw `0` happens to coincide with
boxed integer zero and renders as `0`. That is precisely the tag-confusion
family: a raw scalar deposited in a slot whose reader expects a tagged word.

The `is_ok` / `is_err` arm immediately below (`:1913`) and the arm at `:1896`
use the identical `sextend` idiom and are very likely affected the same way —
**not verified here**, and deliberately not asserted anywhere yet.

Note the tension a fix must resolve: this same lowering feeds both
`if x.is_some():`, where a raw `0`/`1` is what the branch wants, and
`print(x.is_some())`, where a tagged bool is what the renderer wants. The
working control (`contains`, `starts_with`, which print `true` correctly under
JIT) reaches the result through a different path and is the model to follow.
A blind `sextend` -> "box as TAG_SPECIAL bool" swap without checking the
condition-position consumers would trade this bug for a wrong-branch bug.

## Why no spec asserts it yet

The four rows were REMOVED from
`probe_option_presence_falsy_payload.spl` rather than left red, with an inline
comment pointing here, so that probe stays a clean gate for the defect it was
written for. Re-add them when this is fixed — the probe already has the right
shape and the absent/present controls.

## Cross-refs

- `doc/08_tracking/bug/seed_interp_option_match_falls_through_at_scale_2026-07-18.md`
- `doc/08_tracking/bug/parse_family_strips_option_jit_native_2026-08-02.md`
  (both fixed by the `rt_is_none` change that exposed this one)
