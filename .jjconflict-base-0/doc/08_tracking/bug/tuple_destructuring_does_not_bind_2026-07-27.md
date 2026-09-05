# Bug: `val (a, b, c) = <non-tuple>` binds nothing, silently

- **ID:** tuple_destructuring_does_not_bind_2026-07-27
- **Reported by:** lane FSDICT (LLVM/rustc port specs), root-caused by lane TUPLE
- **Status:** OPEN — diagnosis complete, fix NOT applied (live lane GFIX owns `src/compiler_rust/**`)
- **Severity:** HIGH (silent wrong behaviour on the default engine; misleading error on the interpreter)
- **Compiler tree:** `src/compiler_rust/**` (Rust seed — what `bin/simple` currently is)

## Summary

Tuple destructuring in a `val`/`var` declaration is **irrefutable and unchecked**.
When the right-hand side is not a `Value::Tuple`/`Value::Array` — e.g. a struct —
the interpreter binds **zero** names and raises **no error**. The failure surfaces
much later as `semantic: variable 'c' not found`, at whatever line first reads one
of the never-bound names.

The originally reported symptom "destructuring is not binding" is real, but the
trigger is narrower than it looked: **flat tuple destructuring works fine.** The
failing shape is *destructuring a struct as if it were a tuple*.

The concrete trigger in `test/integration/os/port/rust/smoke_rustc_spec.spl` is
that `process.run` does **not** return a tuple:

```
src/lib/process.spl:8   fn run(cmd: text, args: [text]) -> ProcessResult:
src/lib/process.spl:9       val (stdout, stderr, exit_code) = process_run(cmd, args)   # <- the real tuple
```

`process_run` (`std.nogc_sync_mut.io.process_ops`) returns the 3-tuple
`(text, text, i64)`; the `process.run` shim wraps it in a `ProcessResult` struct.
So `val (out, err, code) = process.run(...)` destructures a **struct** and binds
nothing. Correct call sites use either `process_run(...)` (tuple) or
`.stdout` / `.stderr` / `.exit_code` on the `ProcessResult`.

## Truth table

Engine column = which binary/engine produced the row. `bin/simple` is currently
the **Rust bootstrap seed** (it prints the seed banner). "JIT" = default
`bin/simple run`; "INTERP" = `SIMPLE_EXECUTION_MODE=interpreter bin/simple run`.
Repros under `build/tuple_repro/`.

| # | Shape | JIT (`bin/simple run`) | INTERP | Verdict |
|---|-------|------------------------|--------|---------|
| t1 | `val (a,b) = fn() -> (i64,i64)` | `a=1 b=2` | same | PASS |
| t2 | `val (o,e,c) = fn() -> (text,text,i64)` | `o=out e=err c=7` | `o=out e=err c=7` | PASS |
| t3 | same as t2 but `var (...)` | `o=out e=err c=7` | same | PASS |
| t4 | `val (_, _, c) = fn() -> 3-tuple` | `c=7` | same | PASS |
| t5 | **`val (o,e,c) = fn() -> Struct`** | **no output, exit 0, NO error** | **`error: semantic: variable \`o\` not found`** | **FAIL (both, differently)** |
| t6 | nested `val ((a,b),c) = fn() -> ((i64,i64),i64)` | `[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown variable: a while lowering main` then `a=1 b=2 c=3` | `a=1 b=2 c=3` | PASS at runtime; **JIT cannot lower nested tuple patterns** (silent perf/robustness cliff) |
| t7 | destructure inside a non-`main` `fn` | `c=7` | same | PASS |
| t10 | destructure of an extern-backed tuple (`process_ops.process_run`) | `[INFO] JIT compilation failed ... Unknown variable: process_ops` then `c=0 o=hi` | n/a | PASS at runtime; JIT cannot lower module-qualified calls |

Key readings:

- **Flat tuple destructuring is not broken** (t1–t4, t7). Arity, `var`, and `_`
  all behave.
- **Row t5 is the bug.** Two different wrong behaviours for the same source:
  - JIT: program body silently evaporates — **exit 0, zero output, zero
    diagnostics**. This is the dangerous one.
  - Interpreter: a misleading `variable not found` naming the *first* pattern
    element, pointing at the read site rather than the destructure.
- **Row t6** shows nested tuple patterns are unsupported in HIR lowering and
  silently deoptimize to the interpreter.
- Element **tag/payload mis-decoding was tested and is NOT the mechanism** — the
  documented `Some(<i64>)`-style mis-tag family does not apply here. Values that
  do bind are correct; the failure is that nothing binds at all.

## The cross-`it` "leak" — it is NOT environment corruption

FSDICT observed the error "leaking into the NEXT `it` block". Pinned separately:

**Mechanism: call-graph attribution, not leaked state.**

Direct test (`build/tuple_repro/t8_leak_spec.spl`) — bad destructure placed
inside `it B`, with clean examples before and after:

```
  ✓ A: clean example before the bad one
  ✗ B: bad destructure of a struct
    semantic: variable `c` not found
  ✓ C: clean example AFTER the bad one
  ✓ D: second clean example after
4 examples, 1 failure
```

No leak. Subsequent examples pass. A second test with the destructure in a
module-level helper reached through a gate (`t9_gate_spec.spl`) also attributes
correctly to the calling example.

What actually happens in `smoke_rustc_spec.spl`:

- the bad destructure lives at **line 37**, inside the module-level helper
  `has_nightly_rustc()` (lines 35-38);
- `rust_gate()` (line 40) calls it at line 45;
- `rust_gate()` is called from **`it` at line 66** and **`it` at line 89**.

So the `it` at line 87 ("output binary exists after build") — which contains no
destructure at all — fails with `variable 'code' not found`, naming a variable
that appears nowhere in that example. It reads exactly like a leak. It is a
shared broken helper being reached from multiple examples, with the error text
naming a variable from the *callee*, not the *caller*.

**Real defect worth filing on its own:** the diagnostic carries no callee
file:line / call-frame context, which is what makes it read as a leak. Fixing
the primary bug (see below) removes this instance, but the missing frame context
is a general diagnostics gap.

## Root cause (file:line)

`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:772-790`:

```rust
Pattern::Tuple(patterns) => {
    let values: Vec<Value> = match val {
        Value::Tuple(v) => v,
        Value::Array(v) => (*v).clone(),
        _ => Vec::new(),          // <-- struct/object/anything else => EMPTY
    };
    bind_collection_pattern(patterns, values, is_mutable, env);
}
```

`bind_collection_pattern` (`patterns.rs:793-797`) is a `patterns.iter().zip(values.into_iter())`.
With an empty `values` the zip yields **zero** iterations: no names bound, no
error raised, return type is `()` so there is nothing for the caller to check.

Note the asymmetry: the *match-context* binder `bind_pattern`
(`patterns.rs:20-43` → `bind_sequence_pattern`,
`interpreter_helpers/collections.rs:458-475`) **does** return `false` on a
non-sequence value and on an arity mismatch. The `let`/`val` path throws that
signal away.

Call path: `interpreter/node_exec.rs:69` (`Node::Let`) → `node_exec.rs:219`
`bind_pattern_value(...)`; same call from `interpreter_call/block_execution.rs:284`
and `:1091`.

**Parse/AST:** there is no dedicated destructuring node — `val (a,b,c) = e` is
just `LetStmt { pattern: Pattern::Tuple([...]) }`
(`src/compiler_rust/parser/src/ast/nodes/statements.rs:10-24`,
`parser/src/ast/nodes/core.rs:949,955`,
`parser/src/stmt_parsing/var_decl.rs:204`,
`parser/src/parser_patterns.rs:431-454`).

**HIR/JIT side (explains row t5's silent no-output and row t6's deopt):**
`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:131` dispatches to
`lower_tuple_destructuring` (`:1606-1673`):

- `:1631` — `if let Some(HirType::Tuple(types)) = self.module.types.get(tuple_ty)`;
  for a **struct** type this is `None`, and **no diagnostic is emitted**.
- `:1640-1643` — every element then falls back to `TypeId::ANY`.
- `:1646-1658` — emits `HirExprKind::Index { receiver: __tuple_temp, index: Integer(i) }`,
  i.e. a **numeric index into a struct**, meaningless downstream.
- `:1669` — wildcards ignored; **arity mismatch is never checked** (extra
  patterns just index past the end).
- Related: `:1490` — in `lower_pattern_condition_stmt`, `Pattern::Tuple(_)`
  lowers its match test to constant `Bool(true)`; tuple patterns are treated as
  irrefutable everywhere.

## Fix sketch (NOT applied — `src/compiler_rust/**` has live lane GFIX)

Three independent changes; (1) is the minimum to stop the silent failure.

1. **Make the `let`-path binder fail loudly.**
   `interpreter_helpers/patterns.rs:772-790` — replace `_ => Vec::new()` with an
   error. Change `bind_pattern_value` to return
   `Result<(), CompileError>` (or have the `Tuple` arm construct the error) and
   raise on both non-sequence RHS and arity mismatch:
   - non-sequence: `cannot destructure a value of type <T> as a <N>-tuple`
   - arity mismatch: `tuple pattern has N elements but value has M`
   Propagate at the three call sites (`interpreter/node_exec.rs:219`,
   `interpreter_call/block_execution.rs:284`, `:1091`).
   This is the smallest change and turns t5's silent JIT no-op and the misleading
   `variable not found` into one accurate error at the destructure line.

2. **Reject the shape at HIR lowering, before codegen.**
   `hir/lower/stmt_lowering.rs:1631` — when the RHS type is known and is not
   `HirType::Tuple`, emit a lowering error instead of silently falling back to
   `TypeId::ANY` + integer `Index`. Also add the missing arity check near `:1669`.
   This gives a compile-time error rather than a runtime one for the common case
   where the RHS type is statically known (all 22 `process.run` sites qualify).

3. **Attach call-frame context to `variable not found`.** Independent
   diagnostics improvement; removes the "leaks into the next `it`" illusion for
   every future instance of a broken shared helper.

Nested tuple patterns in HIR lowering (row t6) are a separate, pre-existing gap —
file separately, do not bundle.

## Caller-side fix (independent of the compiler fix)

All 22 `val (...) = process.run(...)` sites are wrong today and silently bind
nothing. Each should either call `process_run(...)` (which really does return a
3-tuple) or read `.stdout` / `.stderr` / `.exit_code` off the `ProcessResult`.

Sites (8 files):

```
src/os/port/simpleos_native_build_config.spl
src/os/tools/simplebox/simplebox_build.spl
src/os/port/verify_all.spl
test/02_integration/os/port/rust/smoke_rustc_spec.spl
test/03_system/os/port/disk_boot_spec.spl
test/integration/os/port/llvm/smoke_clang_spec.spl
test/integration/os/port/rust/smoke_rustc_spec.spl
test/system/os/port/disk_boot_spec.spl
```

Owned by lanes FSDICT (port specs) and the `src/os/**` owner — **not** lane TUPLE.

## Blast radius

Owned code (`src/**` excluding `**/vendor/**`, and `test/**`), regex
`\bval|var +\([a-zA-Z_]+ *,`:

| Scope | Destructure sites | Files |
|-------|-------------------|-------|
| `src/**` `val (` | 1,839 | 503 |
| `src/**` `var (` | 10 | — |
| `test/**` `val (` | 5,516 | 1,135 |
| `test/**` `var (` | 13 | — |
| **`= process.run(...)` (known-broken today)** | **22** | **8** |

The 7,378 general sites are *not* all broken — flat tuple destructuring of a real
tuple works (rows t1-t4, t7). The exposure is: any site whose RHS is (or later
becomes) a struct fails **silently on the default engine**. There is no
compile-time or runtime guard today, so a return-type change from tuple to struct
— exactly what `src/lib/process.spl` did — silently breaks every caller with zero
diagnostics.

## Repro

```
build/tuple_repro/t1_fn2.spl        2-tuple, plain fn
build/tuple_repro/t2_fn3.spl        3-tuple (text,text,i64)
build/tuple_repro/t3_var.spl        var instead of val
build/tuple_repro/t4_underscore.spl wildcard elements
build/tuple_repro/t5_struct.spl     THE BUG: struct RHS
build/tuple_repro/t6_nested.spl     nested tuple pattern
build/tuple_repro/t7_infn.spl       inside a non-main fn
build/tuple_repro/t8_leak_spec.spl  cross-`it` leak test (no leak)
build/tuple_repro/t9_gate_spec.spl  gated-helper attribution test
build/tuple_repro/t10_extern.spl    extern-backed tuple
```

Minimal:

```simple
struct Res:
    stdout: text
    stderr: text
    exit_code: i64

fn mk() -> Res:
    Res(stdout: "o", stderr: "e", exit_code: 7)

fn main():
    val (o, e, c) = mk()
    print("o=" + o + " c=" + c.to_text())
```

`bin/simple run` → exit 0, no output, no error.
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run` → ``error: semantic: variable `o` not found``.
Expected: an error at the destructure line saying a `Res` cannot be destructured
as a 3-tuple.

## Regression spec

`test/01_unit/compiler/tuple_destructuring_spec.spl` — locks in the working flat
cases (t1-t4, t7) and documents the struct case as pending until the fix lands.
