# A local array named `vec` turns `vec[i] = x` into a vector-literal lvalue

- **Filed-on:** 2026-09-05
- **Area:** compiler / parser + HIR lowering (Rust seed)
- **Priority:** P2
- **Status:** open

## Symptom

```
var vec: [f64] = []
var i = 0
while i < 4:
    vec.push(0.0)
    i = i + 1
vec[0] = 1.0          # <-- not an index assignment
```

Runtime: `error: semantic: invalid assignment: unsupported assignment target`,
preceded by the JIT diagnostic that names the cause outright:

```
MIR lowering error: Unsupported HIR construct: complex lvalue:
  VecLiteral([HirExpr { kind: Binary { op: Add, ... } }])
```

`vec[...]` on the left of `=` is parsed as a **vector literal** rather than as
indexing into the local named `vec`. Renaming the local (to `basis`, `q`,
anything else) makes the identical code work. `vec.push(...)` and reads like
`x = vec[0]` are unaffected — only the assignment target mis-parses.

## Why it matters

The failure surfaces far from the cause: the module loads, other functions in
it run, and the error appears only when the offending function is first called,
with a message that does not mention `vec` at all. It cost an hour to localise
while implementing `syevd` in
`src/lib/nogc_async_mut/linalg/mod.spl`; `vec` is an entirely natural name for
an eigenvector accumulator.

Either `vec` should be reserved and rejected at declaration, or — better —
`ident[expr] = value` should resolve `ident` as a variable when one is in
scope, ahead of any literal-form interpretation.

## Workaround in force

`syevd` names its accumulator `basis` and carries an inline NOTE saying why.

## Verification lane

`src/compiler_rust/target/debug/simple run <file>` (debug Rust seed from
current source).
