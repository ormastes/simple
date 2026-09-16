# Interpreter ignores concrete annotation on an `any?` initializer (divergence)

**Date:** 2026-09-01. **Status:** OPEN. **Found while fixing:** MIR-side
`any?` receiver-type erasure (fixed in `src/compiler/50.mir/mir_lowering_stmts.spl`,
early-Let path; regression spec `test/01_unit/bugs/anyq_receiver_erasure_spec.spl`).

## Shape (2 files, measured on the Rust seed interpreter)

```simple
# helper.spl
fn get_obj(x: any) -> any?:
    Some(x)

# main.spl
val d: Dict<text, i64> = get_obj({"a": 1, "b": 2})
d["a"]   # interpreter: "semantic: invalid operation: cannot index value of type enum"
```

The interpreter binds `d` to the raw `Some(...)` enum handle — the explicit
concrete annotation neither unwraps nor retypes the binding, and the first
use dies at RUNTIME. Also reproduces single-file.

## Divergence

Native codegen (post-fix) unwraps via `rt_unwrap_or_self` (Some -> payload,
nil -> tagged nil sentinel, non-Option -> unchanged) and the program runs
correctly (verified by executing the built binary: keys iterate, values
correct). The interpreter errors. Same source, different outcomes — the
interpreter side needs the matching unwrap-on-concrete-annotation, or the
frontend should reject the bare form so both modes agree loudly.

Workaround accepted by both modes today: `... = get_obj(...) ?? {}`.
