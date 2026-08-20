# BUG: JIT SEGV — `!` unwrap of an optional CLASS, then a field access

Status: FIXED 2026-08-20 (fix in tree, NOT yet deployed to the shared seed)
Severity: P1 — crashed the process and blocked all pushes

## Symptom

`bin/simple run` SEGV'd (rc=139, core dumped, **no output at all**) on any
`optional-class unwrap followed by a field access`. The interpreter
(`SIMPLE_EXECUTION_MODE=interpret`) ran the same source cleanly.

This took `b_class_optional_field` out of the class-identity seed matrix, so
`sh scripts/check/check-class-identity-seed-matrix.shs` reported
`FAIL — incomplete matrix over 11 discovered case(s)`
(`seedJIT=10/11 seedINTERP=11/11`) and blocked every push behind it.

Pre-existing, not caused by any recent landing: reproduced identically on the
deployed seed, on the pre-deploy backup binary
(`bin/release/x86_64-unknown-linux-gnu/simple.prefix-backup-0549`), and on a
clean `origin/main` worktree with no local commits.

## Minimisation

The corpus case named an *optional field*, but the field is incidental. The
crashing ingredient is **unwrap-then-field**, and an optional LOCAL crashes too:

| probe | result (pre-fix, JIT) |
|---|---|
| construct `Holder(maybe: c)` | OK |
| read `oh.maybe` | OK |
| `if m.?:` (nil test) | OK — prints `some` |
| `val u = m!` alone | OK |
| `u.n` where `u = m!` | **SEGV** |
| `m!.n` | **SEGV** |
| `val m: Cell? = c` (local, no field) then `m!.n` | **SEGV** |

So `.?` was already correct and `!` alone was already correct; only `!` whose
result is then *dereferenced* was wrong.

## Root cause

The fault is inside JIT-emitted machine code, not in the compiler. gdb:

```
Thread 2 received signal SIGSEGV
#0  0x00000560ea5b2577 in ?? ()          <- JIT-emitted code
#4  simple_compiler::codegen::jit::JitCompiler::call_i64_void ()
#5  ...LocalExecutionManager as ExecutionManager>::execute ()
#6  simple_driver::exec_core::ExecCore::run_file_jit ()
```

`Expr::ForceUnwrap` lowers via `lower_try`
(`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:217` ->
`hir/lower/expr/control.rs:2316`), which assumes its subject is a
`Result`/`Option` **enum** and emits `rt_enum_check_discriminant` +
`rt_enum_payload`.

A nullable is not that. `Cell?` is `HirType::Pointer { inner: Struct Cell }`,
`result_like_payload_type` returns `None` for it
(`control.rs:15-38`), and its runtime value **is the object reference itself**,
with nil as the absent case — which is exactly why `m.?`, a nil test, already
worked.

`control.rs:2333` already carried a guard for precisely this defect class, added
for scalar nullables in
`jit_optional_i64_payload_reinterpreted_2026-08-17.md` — but its allowlist was
scalars only (`BOOL`, `I8..U64`, `F32`, `F64`, `STRING`). A **class** pointee
fell straight through to the enum path. So the JIT asked a plain object pointer
for its `rt_enum_payload`, took the garbage word that came back as a live
reference, and the following field access dereferenced it.

Nothing crashed until the dereference, which is why `val u = m!` alone survived:
the bad word was merely copied around.

## Fix

`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2360-2385` — extend
the existing non-enum-nullable identity guard to a `HirType::Struct` pointee
(classes lower to `Struct`). Unwrapping is the identity on the value; only the
static type narrows from `T?` to `T`.

One deliberate difference from the scalar arm directly above it: the scalar arm
reports `TypeId::ANY` because its word is a *tagged* scalar, whereas this arm
reports the concrete `pointee`. The word here is a real object reference, and
the concrete type is what lets the following `.field` resolve against the right
layout.

## Reproduce + gate

- Fixture: `test/fixtures/repro/compiler/optional_class_unwrap/optional_class_unwrap_field.spl`
- Gate: `sh scripts/check/check-optional-class-unwrap-field.shs`

Validated in both directions against real binaries:

| binary | verdict |
|---|---|
| pre-fix seed (59,860,352 bytes, 2026-08-20 05:54) | `FAIL — 2 engine(s) executed, offender(s): jit:crash(rc=139)` (exit 1) |
| post-fix build (59,699,728 bytes, 2026-08-20 06:13) | `PASS — 2 engine(s) executed, 0 crashes, unwrap-then-field holds` (exit 0) |

**The reproduce is a PROBE (`simple run`), not a spec, on purpose.** Written as
a spec, this reproduce printed "0 failures" on a provably broken binary — a spec
body may not reach the JIT at all. The gate reads the process exit status
directly into a variable on the line after the invocation, never through a pipe.

The gate asserts checks 1 and 2 on both engines but only REPORTS the
"optional holds the reference" check on the interpreter, because the seed
interpreter answers COPY there for separately-tracked reasons (see below).

## Seed matrix, after the fix

```
binary:   /mnt/data/.jitfix-target/release/simple   (59,699,728 bytes, 2026-08-20 06:13)
b_class_optional_field       | REF                            | COPY(n=110)
readings: cases_discovered=11 seedJIT=11/11 seedINTERP=11/11
PASS — complete SEED matrix over 11 case(s)
```

`b_class_optional_field` now produces a real verdict, and the verdict is the
CORRECT one (`REF` — the optional holds the reference), not merely a non-crash.

## Not fixed here (pre-existing, already tracked)

The matrix still shows JIT/interp semantic divergence. Both families have open
records; neither is caused or worsened by this change:

- JIT `REF` vs interp `COPY(n=..)` on all five class cases —
  `interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10.md`,
  canonical record
  `interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`.
- JIT `ALIAS(n=31)`/`ALIAS(n=71)` vs interp `VAL` on `i_struct_returned` /
  `k_struct_method_returned` —
  `jit_struct_assignment_aliases_not_copies_2026-08-10.md` (OPEN P2).

## Deployment note

The fix was built and verified in a PRIVATE target dir
(`/mnt/data/.jitfix-target`). The shared `bin/release/**` seed was deliberately
NOT redeployed — other sessions are live on this box. A seed refresh is needed
before the guard goes green for everyone.

Build-environment note for whoever redeploys: `cargo build` currently fails in
this worktree with `did not expect repo at .../.git to be bare` — `.git/config`
carries `bare = true`, set by another session. Building from a symlink-mirrored
root outside the repo works around it without mutating shared state.
