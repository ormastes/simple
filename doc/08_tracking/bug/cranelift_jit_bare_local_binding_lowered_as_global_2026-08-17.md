# Cranelift JIT silently falls back to the interpreter for ANY keyword-less local binding

- **Filed:** 2026-08-17 (lane CRANELIFT)
- **Status:** OPEN — filed, not fixed (fix is not small/certain; see Root cause)
- **Severity:** P1 — silent loss of the native backend. No wrong result observed; the
  interpreter fallback produces the correct answer, and the process exits **0**.

## Engine distinction (read this first)

- `bin/simple test` is the **tree-walk interpreter** and never reaches the Cranelift
  JIT lane. A spec body **cannot** exercise this defect; any "proof" via
  `simple test` is worthless here.
- `bin/simple run` is the **Cranelift JIT**. Only a script driving `bin/simple run`
  reproduces this.
- Binary tested: `bin/simple`, which is the **Rust SEED** (it prints the seed warning
  banner on stderr). This finding attributes to the SEED codegen path.

## Minimal reproducer

```
fn main():
    o = 5
    print(o)
```

`bin/simple run r.spl`:

```
[CODEGEN BODY] Function 'main' body compilation failed: GlobalLoad: unresolved identifier 'o' (not a global, function, const-data name, or import)
[CODEGEN-STUB-FALLBACK] body compilation failed for 'main': ModuleError("GlobalLoad: unresolved identifier 'o' (not a global, function, const-data name, or import)")
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: codegen: 1 function body/bodies failed to compile: [main]; set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs instead (unsafe — binary will silently misbehave)
5
```

**Exit code is 0.** Nothing on the success path tells the caller the native backend
was abandoned.

## Minimisation (one variable changed at a time)

The originally reported program was:

```
struct Opt:
    path: text
    paths: [text] = []

fn main():
    o = Opt(path: "p")
    print("len={o.paths.len()}")
```

None of the suspected features is the trigger:

| variant | JIT fails? |
|---|---|
| `o = 5` / `print("v={o}")` | **YES** |
| `val o = 5` / `print("v={o}")` | no |
| `var o = 5` / `print("v={o}")` | no |
| `o = 5` / `print(o)` (no interpolation) | **YES** |
| struct + default array field, but `val o = Opt(path: "p")` | no |
| struct with **no** default field, `o = Opt(path: "p")` | **YES** |
| `o = [1, 2]` / `print("n={o.len()}")` | **YES** |
| `o = "x"` / `print("n={o.len()}")` | **YES** |
| `a = 5; b = a + 1` | **YES** |
| bare binding inside a non-`main` function | **YES** |
| `val a = 5; a2 = a` | **YES** |

**Minimal trigger: a function-local binding written WITHOUT the `val`/`var`
keyword.** Nothing about structs, default initializers, named-arg constructors,
string interpolation, `.len()`, or the identifier name `o` matters. `val` and `var`
both compile cleanly.

## Blast radius

Every function in every module that contains at least one keyword-less local
binding loses Cranelift codegen entirely — the whole function body is dropped, not
the one statement — and the run silently degrades to the tree-walk interpreter.
Since `name = expr` without `val`/`var` is an accepted and commonly written form in
this language, the effective blast radius is "most non-trivial `bin/simple run`
programs". Under `SIMPLE_ALLOW_STUB_FALLBACK` the same programs would get an
**empty stub** body instead, i.e. silently wrong results.

## Root cause / codegen location

- Error text: `src/compiler_rust/compiler/src/codegen/instr/mod.rs:498-502`
  (the deliberate fail-closed arm added for
  `jit_run_exits_zero_and_silent_on_semantic_error_2026-08-04.md`). Codegen is
  behaving correctly here — it is being handed a `GlobalLoad` for a local.
- The real defect is upstream, in HIR name resolution / MIR lowering: a bare
  `name = expr` whose name was never declared is classified as
  `HirExprKind::Global`, and MIR lowering takes the `HirExprKind::Global` arm at
  `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:795-809`, emitting
  `GlobalStore`/`GlobalLoad` for what is a function-local slot. `val`/`var`
  declare the local, so they take the local `_ =>` arm at line 812 and work.
- **Not fixed here**: the correct fix is to make the resolver declare an implicit
  local on first bare assignment inside a function body, which interacts with
  genuine module-global assignment, with the "cannot reassign to immutable
  variable" semantic check (a bare rebinding in a loop already errors), and with
  the module-init dynamic pass. That is not a small, certain, single-line change,
  so per the lane rules it is filed rather than half-fixed.

## Reproduction script (not added to the repo)

Scratchpad only. Recreate with the three-line minimal program above and run
`bin/simple run`. Do NOT try to gate this with a `*_spec.spl` — the spec runner is
the interpreter and will pass regardless.
