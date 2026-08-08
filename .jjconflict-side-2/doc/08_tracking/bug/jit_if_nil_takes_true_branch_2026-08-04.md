# JIT: `if nil:` takes the TRUE branch — a nil condition is truthy under Cranelift, falsy under the interpreter (2026-08-04)

**Status:** OPEN
**Found:** 2026-08-04
**Related:** `bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04.md`
(parallel lane, unit tier) records the JIT re-tagging a wrong-typed `bool`
parameter into `<special:N>`; this file isolates the branch-condition half — a
plain nil in `if x:` — which is the same engine, and the two should be fixed
together. Feeder defect:
`optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`.
**Class:** silent wrong answer / engine divergence (JIT vs interpreter).

Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple` — which on this
tree is the **Rust seed** (`bin/simple --version` prints the seed banner and the
file is byte-identical in role to `src/compiler_rust/target/bootstrap/simple`).

## Symptom

```
$ cat r3.spl
fn takes_bool(b: bool) -> text:
    if b:
        return "TRUE"
    return "FALSE"

fn takes_any(b) -> text:
    if b:
        return "TRUE"
    return "FALSE"

fn main():
    val n: i64? = nil
    if nil:
        print "  nil is TRUTHY"
    if n.?:
        print "  n.? TRUTHY"
    print "C takes_bool(nil) = {takes_bool(nil)}"
    print "D takes_any(nil)  = {takes_any(nil)}"
    print "E takes_bool(n.?) = {takes_bool(n.?)}"
    print "F takes_bool(false) = {takes_bool(false)}"
```

`bin/simple run r3.spl` (JIT — the default engine for `run`):

```
  nil is TRUTHY            <-- WRONG
C takes_bool(nil) = TRUE   <-- WRONG
D takes_any(nil)  = TRUE   <-- WRONG
E takes_bool(n.?) = TRUE   <-- WRONG
F takes_bool(false) = FALSE
```

`SIMPLE_EXECUTION_MODE=interpreter bin/simple run r3.spl`:

```
C takes_bool(nil) = FALSE  <-- correct
D takes_any(nil)  = FALSE  <-- correct
E takes_bool(n.?) = FALSE  <-- correct
F takes_bool(false) = FALSE
```

Expected in both engines: a nil condition is falsy. `doc/07_guide/quick_reference/
syntax_quick_reference.md:620` fixes this contract — it defines `opt.is_none()`
as `not opt.?`, which is only true if a nil `.?` result is falsy.

## Root cause (what is PROVEN)

Proven by the A/B above, not by reading codegen:

1. The divergence is **engine-local**, not front-end. The same source, same
   binary, same AST; only `SIMPLE_EXECUTION_MODE` differs, and only the JIT is
   wrong. So the branch-condition truthiness test in the Cranelift lowering path
   is the defect, not the parser or HIR.
2. It is **not** a `.?` defect. `.?` itself is correct on both engines and
   matches the documented `T?` contract:
   `o.?=99  n.?=nil  t.?=hi  e.?=nil` (interpreter, and JIT agrees).
   Line `B` above proves the *inline* form `if n.?:` branches correctly on the
   JIT too — the wrong answer appears only once the nil has been **stored into a
   variable or bound to a parameter** and the condition is a plain value load.
   That narrows it to the generic "value -> branch condition" test, not the
   ExistsCheck lowering (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2895`
   is the ExistsCheck arm and is *not* implicated).
3. `false` still branches correctly (line `F`), so the boolean path is intact;
   only the nil sentinel is mis-tested. This is consistent with the branch test
   being a bare "non-zero" check against a nil sentinel whose encoding is `3`
   (see `.claude/memory/ref_*` on the nil-sentinel-3 encoding), which is
   non-zero and therefore reads as true.

## Blast radius

Any `if x:` / `while x:` / `and` / `or` where `x` is a nil-valued variable or
parameter silently takes the wrong branch under the JIT. `bin/simple run` uses
the JIT by default, so this affects ordinary program execution. It does **not**
affect `bin/simple test`, which hard-defaults to the interpreter — meaning the
entire spec suite is structurally blind to this bug (same class as
`run_vs_test_harness_divergence_2026-07-28.md`).

## Why not fixed now

The fix belongs in the Cranelift branch-condition lowering inside the **Rust
seed** (`src/compiler_rust/compiler/src/codegen/`), not in pure-Simple source.
Changing it requires a `--full-bootstrap` cargo rebuild, and the truthiness rule
it encodes is repo-wide calling-convention semantics: making the nil sentinel
falsy at every branch site needs a decided answer for the other falsy-candidate
values (`0`, `""`, empty collections) so the JIT and the interpreter converge on
one table rather than two. That is a language-semantics decision plus a seed
rebuild, which this lane could not land safely alongside live parallel sessions.
