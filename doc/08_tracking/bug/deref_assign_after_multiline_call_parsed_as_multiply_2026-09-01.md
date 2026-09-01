# `*ptr = v` after a multi-line call is parsed as multiplication

- **Filed:** 2026-09-01
- **Status:** OPEN
- **Blocks:** the riscv64 WM/display closure — this is the NEXT stop after the
  `clobber("memory")` parse defect
  (`riscv64_wm_closure_unbuildable_asm_clobber_string_2026-09-01.md`) was fixed.

## Symptom

```
Build failed: failed to parse src/os/kernel/arch/riscv64/interrupt.spl
at 349:24 during discovery: Unexpected token: expected expression, found Assign
```

`interrupt.spl:349` is `*scheduler = state.scheduler`, and column 24 is the `=`.

## Root cause (reduced, both fixtures run on a freshly built seed)

Deref-assignment ALONE parses:

```simple
fn f(p: rawptr<i64>, v: i64):
    *p = v          # parses
```

It stops parsing when the preceding statement is a call whose argument list
spans lines — exactly the shape at `interrupt.spl:347-349`:

```simple
fn f(p: rawptr<i64>, v: i64):
    val s = g(
        1)
    *p = v          # "expected expression, found Assign"
```

The leading `*` of the next statement is absorbed as a binary multiply
continuing the previous expression (`g(...) * p`), and the parser then wants an
expression where the `=` is. So this is a statement-boundary/continuation
defect, not a missing deref-lvalue grammar.

## Second, independent defect found by the same fixture

Even where `*p = v` DOES parse, native codegen cannot lower it:

```
MIR lowering error: Unsupported HIR construct:
complex lvalue: Deref(HirExpr { kind: Local(0), ty: TypeId(14) })
```

The JIT drops the whole module to the interpreter. A freestanding kernel has no
interpreter to fall back to, so this will surface as a hard failure on the
riscv64 lane once the parse defect above is fixed. Both must be fixed before
`os.kernel.arch.riscv64.interrupt` can be part of a native kernel closure.

## Affected sites (tree-wide, 4)

- `src/os/kernel/arch/riscv64/interrupt.spl:349,350`
- `src/compiler_rust/lib/std/src/core_nogc/bump.spl:121`
- `src/compiler_rust/lib/std/src/core_nogc/arena.spl:148`

## Not taken here

Not fixed in this change, which owns the inline-asm clobber grammar. Recorded
rather than worked around: per CLAUDE.md, a short safe grammar form that fails
gets fixed or filed, never silently normalized. Rewriting the two riscv64 sites
into some other spelling would hide a real parser defect that also affects the
stdlib arena/bump allocators.
