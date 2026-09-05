# Unsafe-context enforcement: port plan (P1 id=557)

Date: 2026-07-27
Status: **PLAN — deliberately not implemented.** See "Why not a contained fix".

## 1. The defect as filed, and how it differs from reality

P1 id=557 (`doc/09_report/todo_p1_live_db_triage_2026-07-27.md`) states: the Rust seed
has an `UnsafeBlock` HIR node but no `in_unsafe` enforcement, while the pure-Simple
compiler implements enforcement in `src/compiler/35.semantics/safety_checker.spl`.

The first half is confirmed. **The second half is not.** The Simple-side pass exists
and is correct, but it has **zero callers** — it is exported and never run:

```
$ grep -rn 'SafetyChecker\|safetychecker_check_module' --include=*.spl .
src/compiler/35.semantics/__init__.spl:68:   export use ... .{SafetyError, SafetyContext, SafetyChecker}
src/compiler/35.semantics/safety_checker.spl:  (definitions only)
```

`safetychecker_check_module` is defined at `safety_checker.spl:61` and invoked
nowhere. `SafetyChecker.create()` is called nowhere.

So there is **no seed-vs-self-hosted divergence today**. Both compilers accept inline
asm outside `unsafe`. The real state is a *shared, silent* gap: one side has the
checker written but dead, the other never had one.

This reframes the fix. Adding enforcement to the Rust seed alone would *create* the
divergence — the seed would reject code the self-hosted compiler accepts, and (per
`doc/08_tracking/bug/seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md`)
that class of mismatch surfaces only at stage 4, after hours of build.

## 2. What the Simple side actually enforces (when run)

`src/compiler/35.semantics/safety_checker.spl`.

**Context tracking** — a single `bool` on a struct field, with save/restore, not a
depth counter and not a stack:

```
struct SafetyContext:
    in_unsafe: bool
    errors: [SafetyError]
```

`safety_checker.spl:133-138`:

```
case UnsafeBlock(body):
    val was_unsafe = self.context.in_unsafe
    self.context.in_unsafe = true
    safetychecker_check_block(self, body)
    if not was_unsafe:
        self.context.in_unsafe = false
```

Nesting is handled correctly (restore-to-previous, so an inner block exiting does not
clear an outer block's context). `in_unsafe` is a property of the *lexical* HIR walk
only — it does **not** propagate into called functions, and there is no notion of an
`unsafe fn`.

**Restricted operation set — exactly one operation.** Despite the file header
comment claiming three ("inline assembly", "raw pointer operations", "SFFI calls"),
the only rule implemented is:

| Operation | HIR node | Diagnostic |
|---|---|---|
| Inline assembly | `HirExprKind.InlineAsm(HirAsm)` | `SafetyError.InlineAsmOutsideUnsafe(span)` |

`safety_checker.spl:141-143`:

```
case InlineAsm(asm_code):
    if not self.context.in_unsafe:
        self.context.errors = self.context.errors.push(SafetyError.InlineAsmOutsideUnsafe(expr.span))
```

The other two `SafetyError` variants — `UnsafeFfiOutsideUnsafe`, `RawPointerOutsideUnsafe`
(`safety_checker.spl:20-21`) — are **declared and never constructed**. There is no
raw-pointer rule and no SFFI rule anywhere in the pass.

Also unchecked by the walk: `InlineAsmMatch` (`hir_definitions.spl:520`) has no case
in `safetychecker_check_expr`, so `asm match:` escapes the check entirely even when
the pass is run. The walk's trailing `case _: pass` makes every unhandled variant a
silent false negative.

**Emission**: errors accumulate into `self.context.errors` and are returned from
`safetychecker_check_module`. There is no span formatting, no error code, and no
integration with `CompileContext.errors`.

## 3. Rust seed: verified state

`grep -rn 'in_unsafe\|unsafe_depth' src/compiler_rust/` → **zero hits** outside
`vendor/` (the only `is_unsafe` hits are `mir/effects.rs:197,632`, an unrelated
effect-lattice predicate, and `effects.rs:191 is_unsafe_operation`, a name-table
lookup for the `@unsafe` *effect* annotation — neither consults block context).

`UnsafeBlock` survives the whole pipeline but is semantically transparent:

| Stage | File:line | Treatment |
|---|---|---|
| Parse | `parser/src/parser_impl/core.rs:834` | `Expr::UnsafeBlock(block.statements)` |
| AST node | `parser/src/ast/nodes/core.rs:769` | `UnsafeBlock(Vec<Node>)` |
| HIR lower | `compiler/src/hir/lower/expr/mod.rs:186` → `expr/control.rs:913` | `HirExprKind::UnsafeBlock(block_stmts)` |
| HIR node | `compiler/src/hir/types/expressions.rs:114` | `UnsafeBlock(Vec<HirStmt>)` |
| MIR lower | `compiler/src/mir/lower/lowering_expr.rs:234` | `=> self.lower_block_expr(stmts)` — **identical to a plain block** |

Every other site treats it as an alias for `Block`: `security.rs:1371`,
`hir/lower/module_lowering/validation.rs:157`, `contract.rs:60`, `compilability.rs:711`,
`symbol_analyzer.rs:288`, the lint checkers, the interpreter. The pattern is always
`HirExprKind::Block(stmts) | HirExprKind::UnsafeBlock(stmts) =>`.

**Structural mismatch that any port must handle**: the Rust HIR models inline asm as a
**statement** — `HirStmt::InlineAsm { instructions: Vec<String>, volatile: bool }`
(`compiler/src/hir/types/statements.rs:100-103`, produced at
`hir/lower/stmt_lowering.rs:768`) — while the Simple HIR models it as an **expression**
kind, `HirExprKind.InlineAsm(HirAsm)` (`20.hir/hir_definitions.spl:517`, produced at
`20.hir/hir_lowering/expressions.spl:836`). The Rust `HirStmt::InlineAsm` also carries
**no span**, so the diagnostic cannot point at the offending asm without first adding
one.

## 4. Why not a contained fix

Turning the rule on — in either compiler — is a **breaking migration, not a checker
addition**. Static blast-radius measurement over owned code (`src/lib`, `src/os`,
`src/runtime`; vendored paths excluded per CLAUDE.md § Owned-Code Scope):

- 38 files contain real inline-asm sites.
- **At least 23 of them contain no `unsafe:` block at all** — roughly 60 asm sites
  that would immediately become hard errors.

Representative, all currently legal and all load-bearing for boot:

| File | asm sites | `unsafe:` blocks |
|---|---|---|
| `src/lib/nogc_async_mut_noalloc/baremetal/x86/io.spl` | 6 | 0 |
| `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 6 | 0 |
| `src/lib/nogc_async_mut_noalloc/baremetal/riscv/semihost.spl` | 6 | 0 |
| `src/os/userlib/syscall_raw.spl` | 3 | 0 |
| `src/os/kernel/scheduler/address_space_switch.spl` | 5 | 0 |
| `src/os/kernel/scheduler/context_switch.spl` | 2 | 0 |
| `src/os/kernel/arch/riscv64/trap_vector.spl` | 2 | 0 |
| `src/lib/.../baremetal/x86/{idt,gdt}.spl`, `arch/{riscv64,riscv32,arm64}/boot.spl` | 1 each | 0 |

e.g. `x86/io.spl:12` — `asm volatile("out dx, al", in(dx) port, in(al) value)` — at
function top level, no enclosing `unsafe:`.

Shipping a fatal check here breaks the SimpleOS build on the first compile. Shipping it
Rust-only additionally manufactures the exact seed-vs-self-hosted split that cost this
project a full day on 2026-07-27. Neither can be validated here: bootstrap and the test
suite are both out of scope for this session, so the true diagnostic count is unknown
and the number above is a lower bound from grep, not a compiler count.

**The repo already has a convention for precisely this situation.** `driver.spl:970-989`
and `run_typecheck_warn_pass` (`driver.spl:1292-1321`) wire two other
fully-implemented-but-never-called checkers (`HmInferContext.infer_module`,
`check_module_visibility`) as a **warn-only, env-gated** pass that logs and never
pushes to `ctx.errors`, explicitly so the blast can be measured before fatal wiring.
The comment there states the reasoning verbatim: *"They have never run over the full
~993-module set, so their true diagnostic count is unknown and enabling them fatal
would very likely break the build."* That applies unchanged here. This plan follows it.

## 5. The port, in order

**Rule 0 — the two compilers' rules must agree, and must land together.** Any change to
the restricted-operation set, the context-tracking semantics, or the diagnostic must be
applied to `src/compiler/35.semantics/safety_checker.spl` and the Rust seed in the same
commit. A seed that is stricter than the self-hosted compiler is a stage-4 landmine; a
seed that is looser is the current silent gap. Precedent:
`doc/08_tracking/bug/seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md`.

### Step 1 — Simple side, warn-only wiring (small; unblocks measurement)

- Add `safetychecker_check_module` to `run_typecheck_warn_pass`
  (`src/compiler/80.driver/driver.spl:1303`), formatting each `SafetyError` as
  `[safety] {module}: inline asm outside unsafe block at {span}`. Push to the returned
  `[text]`, never to `ctx.errors`. Reuses the existing `SIMPLE_TYPECHECK_WARN=1` gate,
  so the default build is unaffected.
- Fix the known false negative first: add a `case InlineAsmMatch(arms):` to
  `safetychecker_check_expr` that walks each arm's body and flags it outside unsafe.
- Effort: ~1h edit, plus one bootstrap to run it. Output is the real violation count.

### Step 2 — Rust side, matching warn-only checker

- New `src/compiler_rust/compiler/src/hir/analysis/unsafe_checker.rs`, following the
  `ghost_checker.rs` convention exactly: `pub struct UnsafeChecker<'a> { module: &'a HirModule, .. }`,
  `pub fn new(module) -> Self`, `pub fn analyze(self) -> UnsafeAnalysisResult`,
  `pub fn to_compile_errors(&self) -> Vec<CompileError>`, `#[cfg(test)] mod tests` at the
  bottom. Register in `hir/analysis/mod.rs` alongside `ghost_checker`.
- **Prerequisite**: add a span to `HirStmt::InlineAsm` (`hir/types/statements.rs:100`)
  and populate it at `hir/lower/stmt_lowering.rs:768`. Without this the diagnostic has
  no location. This is the single most invasive part — `HirStmt::InlineAsm` is
  constructed in one place but matched in several (`codegen/`, `mir/`, `pretty_printer.rs`).
- **Traversal**: a `bool in_unsafe` threaded as a parameter through paired
  `check_stmt(&self, stmt, in_unsafe)` / `check_expr(&self, expr, in_unsafe)` walkers —
  matching the Simple side's save/restore semantics, not a depth counter.
  `HirExprKind::UnsafeBlock(stmts)` recurses with `true`; everything else forwards the
  incoming value. Critically, the walk must **split** the ubiquitous
  `HirExprKind::Block(stmts) | HirExprKind::UnsafeBlock(stmts)` pattern — that alias is
  the reason the node is currently inert. Copy the variant list from
  `security.rs:collect_hir_expr_symbols` (the most complete existing HIR walk) so the
  new walker has full coverage; do **not** use a `_ => {}` arm, use an explicit
  exhaustive match so future HIR variants fail to compile rather than silently escaping.
- **Restricted set for v1: `HirStmt::InlineAsm` only** — exactly the Simple side's
  single implemented rule. Do not add raw-pointer or SFFI rules here; adding them means
  adding them to `safety_checker.spl` in the same commit (see Rule 0) and re-measuring.
- **Invocation**: warn-only behind an env gate mirroring `SIMPLE_TYPECHECK_WARN`. Do not
  call it from `Lowerer` where a `LowerError` would abort the build.
- Effort: ~1 day including the span plumbing.

### Step 3 — Migration (the actual work)

Wrap the ~60 asm sites in `unsafe:` blocks, file by file, verifying each arch still
boots (x86_64 OVMF, riscv OpenSBI, aarch64) per `.claude/rules/board-runnable.md`. This
is where the risk lives — `boot.spl` / `trap_vector.spl` / `context_switch.spl` changes
are load-bearing for every platform gate. Estimate 2-3 days with board re-verification.

### Step 4 — Flip to fatal, both compilers, one commit

Only after Step 3 reports zero warn-only diagnostics on a full build. Push
`SafetyError`s into `ctx.errors` on the Simple side and return
`Vec<CompileError>` from the Rust checker in the same change. Add a stage-4 smoke case
asserting *both* compilers reject the same minimal program (asm outside unsafe) and
accept the same minimal program (asm inside unsafe) — a divergence test, not just a
per-compiler test.

### Deferred, explicitly out of scope for v1

Raw-pointer and SFFI rules (the two dead `SafetyError` variants), `unsafe fn`
propagation, and any interprocedural notion of unsafe. Each needs its own operation-set
definition and its own blast measurement. Recording them here rather than
half-implementing them is deliberate: the dead variants should either be implemented
with a measured migration or deleted, per CLAUDE.md § "NEVER convert TODO to NOTE".

## 6. Total effort

~4-5 days end to end, dominated by Step 3 (asm-site migration + per-arch board
re-verification), not by the checkers. Steps 1-2 alone are ~1.5 days and produce the
measurement that Step 3 needs.
