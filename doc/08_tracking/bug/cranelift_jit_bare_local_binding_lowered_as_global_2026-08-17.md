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

## Blast-radius census (lane CENSUS, 2026-08-17)

**Headline: 0 confirmed occurrences of this defect shape in owned Simple source.**
This is a real defect with a real reproducer, but it is a *latent grammar trap*,
not a live systemic performance/correctness problem in the current tree.

### Scope

Scanned `src/lib/**`, `src/app/**`, `src/compiler/**`, `src/os/**` — 13,645
`.spl` files. **Excluded per CLAUDE.md Owned-Code Scope:** `src/compiler_rust/vendor/**`,
`src/runtime/vendor/**`, `src/runtime/miniaudio.h`, `src/runtime/stb_image.h`,
`src/runtime/stb_truetype.h`, and any `.vscode-test/` directory. Scans used
`os.walk` (not the repo's wrapped ugrep, which honours `.gitignore` and
under-reports) and ran in the background to avoid truncation.

### Matching rule

A hit is a line inside a function body of the form `NAME = EXPR` where:
- `NAME` is a plain identifier — **not** `d[k] = v`, `a.b = v`, or a call;
- the operator is exactly `=` — excludes `==`, `!=`, `<=`, `>=`, `+=`, `-=`,
  `*=`, `/=`, `%=`, `//=`, `|=`, `&=`, `^=`, `<<=`, `>>=`, `:=`, `=>`;
- carried paren/bracket/brace depth is 0 — excludes multi-line call arguments,
  named/keyword args, struct-literal fields, dict/array literals, default
  parameter values;
- the line is not in a comment or a `"""` docstring;
- `NAME` is **not** a module-level global (`val`/`var`/`const`/`let`/`static [mut]`
  at indent 0) anywhere in owned code — writes to those are legitimate;
- `NAME` was not already introduced in this function by a declaration
  (including `var a = 1; var b = 2` multi-decl lines), a parameter (including
  multi-line signatures), a `for` binder, or a `case`/`catch`/`as` binder.

Assignments to an already-declared local are counted separately as *rebinds* and
are **empirically innocent** (see below): 71,225 of them.

### Funnel — each stage is a false-positive class removed

| stage | hits | FP class eliminated |
|---|---|---|
| naive `^\s*NAME\s*=` (depth/op/comment filtered) | 4,247 | — |
| + `"""` docstring blocks, file-local globals | 313 | doc examples, own-module globals |
| + tree-wide global set, `_` wildcard | 25 | imported/cross-module globals |
| + `;` multi-decl, `static`/`let mut`, multi-line params | 9 | missed declarations |
| + hand-check of all 9 | **0** | params, enclosing-block decls |

**Estimated false-positive rate of a naive regex: ~100%** (a hand-checked random
sample of 20 at the 313-hit stage was 20/20 false positives — all module globals
or imported globals). Of the final 9, hand-checking every one found 7 were
declared locals/parameters my scanner's scoping missed, and 2
(`src/compiler/test/simple_coverage_test.spl:387,396`) are a *different* shape:
a nested `fn` assigning to an outer local (closure capture).

### Empirical confirmation (`bin/simple run` = Cranelift JIT; the Rust SEED)

Attributed to the seed at `bin/release/x86_64-unknown-linux-gnu/simple`, which
prints its own bootstrap-seed warning. `bin/simple test` is the tree-walk
interpreter and cannot exercise this path at all; it was not used as evidence.

| program | result |
|---|---|
| `fn main(): o = 5; print(o)` | **RED** — `GlobalLoad: unresolved identifier 'o'`, JIT falls back, prints `5`, exit 0. Reproducer reconfirmed. |
| `var o = 1` then `o = 5` | GREEN — no JIT failure. Rebinding a declared local is clean. |
| `var a`/`var b`, `b = a + 1` | GREEN |
| `static mut G: i64 = 0`, `G = 7` under `unsafe:` | GREEN — validates the global exclusion |
| nested `fn` assigning outer `called` | JIT fails, but with a **different** error: `unresolved external symbol 'side_effect' would NULL-jump in JIT`. Separate defect, not this one. |

The rebind result is the load-bearing one: it is what keeps 71,225 sites out of
the blast radius. Had rebinds also triggered, this would have been catastrophic.

### Verdict

**Not systemic — a latent trap, correctly filed as a real bug.** Owned Simple
code consistently uses `val`/`var`, so essentially no production function is
currently losing native codegen this way. The severity remains in the *failure
mode*, not the count: silent whole-function interpreter fallback at exit 0, and
silently wrong results under `SIMPLE_ALLOW_STUB_FALLBACK`.

**Recommendation:** do **not** perform any mechanical rewrite — there is nothing
to rewrite. Fix the resolver as the bug body already proposes, and consider a
lint rule so a bare binding is a diagnostic rather than a silent deoptimisation.
Separately, file the closure-capture JIT failure found above; it is a real,
distinct gap with live occurrences.
