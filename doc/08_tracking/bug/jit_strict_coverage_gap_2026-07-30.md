# SIMPLE_JIT_STRICT coverage gap (2026-07-30, part 2 of the fail-open fix)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Follow-up to `doc/08_tracking/bug/jit_strict_fail_open_fix_2026-07-30.md`
(part 1: the tag reached the catch site but nothing else was tagged). This
pass asks the honest question that fix left open: **for the whole JIT
compile pipeline, which failure paths does `SIMPLE_JIT_STRICT=1` actually
catch, and which does it silently pass through?** Prompted by two concrete
misses discovered since: an `Unknown variable: bootstrap_hir_type_from_tag`
HIR-lowering error that de-JITted with no strict-mode hard-fail, and (from a
sibling lane) a silent Cranelift miscompile that produces no error at all —
see the session memory note
`reference_jit_chained_method_to_i64_returns_garbage.md`. **The
deliverable is the shape of the hole, not a claim it is closed.**

## 0. PROVED — the originally-named repro is now unreachable via a *different*, independent fix; this pass covers the error *class*, not just that one instance

`bootstrap_hir_type_from_tag` called as a **function** (`bootstrap_hir_type_from_tag(3)`) does not reach `LowerError::UnknownVariable` at all — it hits row 7 below (`first_unresolved_import`, already tagged since part 1), confirmed by direct run (`[jit-fallback] unresolved external symbol 'bootstrap_hir_type_from_tag'`).

More significantly: `run_file_jit` (`exec_core.rs:731`) was independently changed by a sibling lane, same day, to call
`hir::lower_with_context_lenient_and_project_hint` instead of the strict lowerer (see the adjacent code comment citing
`doc/08_tracking/bug/jit_drawirrendertarget_moduleresolver_gap_2026-07-30.md`). That function sets `lowerer.set_lenient_types(true)`
(`hir/lower/mod.rs:167`). Under `lenient_types`, a **bare unknown identifier** (the `UnknownVariable` sites at
`hir/lower/expr/mod.rs:320`, `hir/lower/expr/inference.rs:61`, and the empty-let-pattern path `stmt_lowering.rs:179`) is no longer an
error at all — it is silently treated as `Global(name)` typed `ANY` (`mod.rs:308-313`) or gets a synthesized name
(`stmt_lowering.rs:170-177`) and lowering proceeds. The error only surfaces later, if that global is ever actually called/resolved,
via the *already-tagged* `first_unresolved_import` guard (row 7) — the exact case above. So for a **bare-identifier** `UnknownVariable`,
this concurrent, independent fix already closed the practical gap by routing it into row 7, before this pass touched anything.

This does not make this pass's fix (§2) redundant. `LowerError` has other variants not gated by `lenient_types` at all —
confirmed live and reachable from `run_file_jit` by direct run below (`Unsupported feature: gpu.barrier() takes no arguments`,
`hir/lower/expr/simd.rs:112`). The fix in §2 tags the whole `HIR lowering error:` / `MIR lowering error:` message class generically
(not one named variant), so it covers this row and every other non-lenient-gated `LowerError`/MIR-lowering-error variant, not just
the one instance originally reported. **Both facts are recorded here because they are both true and neither should be read as
supporting a stronger claim than it does**: the specific named symptom is gone via someone else's fix; the general error class this
pass targets is real, still reachable, and is now tagged.

## 1. PROVED — enumeration of every JIT compile/execute failure path

Traced the full call chain of `run_file_jit`
(`src/compiler_rust/driver/src/exec_core.rs:693-822`) from module load
through `em.execute("main", &[])`, and everything it calls into
(`codegen/jit.rs`'s `compile_module`). Every `Err`-producing step:

| # | Site | Failure | Tagged with `SIMPLE_JIT_STRICT:`? | Behavior today |
|---|---|---|---|---|
| 1 | `exec_core.rs:711` `load_module_with_imports` | module/parse/import-resolution error | No | Untagged `Err`; falls back leniently (would also fail identically in the interpreter fallback, so low practical risk) |
| 2 | `exec_core.rs:731-732` `hir::lower_with_context_lenient_and_project_hint` | `LowerError::UnknownVariable`, `TypeMismatch`, `CannotInferType`, etc. — **the class this pass closes** | **Now yes** (was No before this fix) | Fixed below |
| 3 | `exec_core.rs:735` `lower_to_mir` | MIR-lowering error (same "cannot be JIT-compiled" class as #2) | **Now yes** (was No before this fix) | Fixed below |
| 4 | `exec_core.rs:793-796` generator/`Yield` bail-out | `gen fn` used as top-level entry (JIT state-machine lowering gap, B3) | No — **by design** | Known, documented limitation; interpreter handles generators correctly; not touched (see scoping note below) |
| 5 | `jit.rs:111-118` `first_lambda_function_impl` guard | any `ClosureCreate` in the module (lambda/closure ABI is not tag-boxed — see `jit_lambda_abi_scoping_2026-07-29.md`) | No — **by design** | Known, documented limitation; interpreter gives correct answers; not touched |
| 6 | `jit.rs:121` `self.backend.compile_all_functions(mir)?` | a genuine Cranelift codegen bug (backend `Err` not caused by 1-6 above) | No | Untagged; falls back leniently. Same "genuine compiler bugs" class the part-1 fix's own comment (`exec_core.rs:654-656`) explicitly excluded from scope |
| 7 | `jit.rs:135-160` `first_unresolved_import` guard | unresolved external symbol → would NULL-jump | **Yes** (the original, part-1 fix) | Hard-fails under strict; unchanged by this pass |
| 8 | `exec_core.rs:817` `em.execute("main", &[])` | JIT execution-time error (rare; Cranelift runtime fault surfaced as `Err` rather than a hard crash) | No | Untagged; falls back leniently |
| 9 | `exec_core.rs:640,666-671` outer `catch_unwind` | any Rust `panic!` anywhere in steps 1-8 | No — **cannot be tagged**, a panic has no message to inspect before unwinding is caught | Always falls back leniently with an `[INFO] JIT panicked` message |
| 10 | **Silent miscompile** — JIT compiles and links successfully but computes a wrong answer (e.g. the 2+-hop `.to_i64()` chain bug, exactly 32 apart, see the memory reference above) | *(no failure occurs)* | **N/A — there is no error to tag** | See §3 below |

Rows 2-3 are what this pass fixes. Rows 4-6, 8-9 remain untagged and
fall back leniently — this document does not claim otherwise. Row 10 is
categorically different from every other row and is addressed separately
in §3.

## 2. Fix — extend the tag to the HIR/MIR-lowering-error class

`exec_core.rs:731-732` and `:735` (the two `.map_err(...)?` one-liners for
HIR and MIR lowering) now route through a shared helper,
`jit_strict_fallback_error(kind, err)` (added near
`should_force_interpreter_for_source`, `exec_core.rs`), which mirrors
`jit.rs`'s `first_unresolved_import` convention exactly:

```rust
fn jit_strict_fallback_error(kind: &str, err: &impl std::fmt::Display) -> String {
    eprintln!(
        "[jit-fallback] {kind}: {err}: whole module dropped to the interpreter \
         (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error."
    );
    if std::env::var_os("SIMPLE_JIT_STRICT").is_some_and(|v| v != "0") {
        format!("SIMPLE_JIT_STRICT: {kind}: {err}; refusing to fall back to the interpreter")
    } else {
        format!("{kind}: {err}")
    }
}
```

```rust
let hir_module = match hir::lower_with_context_lenient_and_project_hint(&ast, path, project_hint.as_deref()) {
    Ok(m) => m,
    Err(e) => return Err(jit_strict_fallback_error("HIR lowering error", &e)),
};
let mut mir_module = match lower_to_mir(&hir_module) {
    Ok(m) => m,
    Err(e) => return Err(jit_strict_fallback_error("MIR lowering error", &e)),
};
```

The existing catch site in `run_file_with_args` (`exec_core.rs:642-664`,
untouched by this pass) already checks `jit_err.contains("SIMPLE_JIT_STRICT:")`
and propagates as a real, non-zero-exit error instead of falling back — that
plumbing from the part-1 fix now also serves rows 2-3, with no changes needed
there.

**Scoping discipline (unchanged from part 1, explicitly re-confirmed here):**
only rows 2, 3, and 7 are tagged. Rows 4, 5, 6, 8, 9 — every known,
*documented* JIT limitation (generator lowering, lambda/closure ABI) and every
*undocumented* but still-lenient path (codegen errors, execute-time errors,
panics) — are deliberately left untouched. This is not an oversight: turning
rows 4-5 into hard failures would break the two known-correct, intentional
fallback mechanisms that currently give correct answers via the interpreter
for constructs the JIT cannot yet handle at all — exactly the "must not turn
benign lenient behavior into a hard error" boundary this task was scoped
against. Default (non-strict) behavior for every row is byte-for-byte
unchanged: the only observable difference for `SIMPLE_JIT_STRICT` unset is
that the printed message for rows 2-3 gained a shared `HIR lowering error: ` /
`MIR lowering error: ` prefix format (was already effectively that text,
now routed through one helper instead of two separate `format!` calls).

## 3. What strict mode can NEVER catch (read this before trusting a clean strict run)

Rows 1-9 above are all failures the compiler *knows about* — something
returned `Err`, or panicked, before producing a result. Strict mode's entire
mechanism is "turn a known failure into a hard failure instead of a silent
fallback." It has no mechanism, and can have no mechanism, for **row 10**: a
JIT compile that succeeds, links, and runs to completion but computes the
wrong answer. There is no `Err` anywhere in that path — nothing for any
tag, marker, or strict-mode check to catch.

This is not hypothetical. A sibling lane found exactly this on 2026-07-30: a
function containing two independent chained-method call sites, each 2+ hops
ending in `.to_i64()` (e.g. `a.trim().to_i64()` appearing twice in one
function), returns large garbage for **both** results under the default
Cranelift JIT — always exactly 32 apart, reproduced across 4 independent
runs — with **zero** `[jit-fallback]` marker, no unresolved-symbol error, no
panic. `SIMPLE_JIT_STRICT=1` changes nothing about this run: it compiles,
links, finalizes, and executes "successfully," producing a wrong number.
Full repro and bisection: the memory reference cited above; a pinned
regression spec exists at
`test/01_unit/lib/language/chained_method_i64_conversion_spec.spl`.

**The inference this document exists to kill:** "I ran with
`SIMPLE_JIT_STRICT=1` and got no error, therefore the JIT result is
correct." That inference is false, has already misled this campaign once
(the `.to_i64()` bug was initially chased as a different bug class,
`pixels.len()` returning 0, before the actual defect was isolated), and
will mislead it again if repeated. Strict mode narrows *one* failure mode
(silent whole-module fallback) into a loud one. It says nothing about
correctness of code that successfully finishes compiling.

## 4. Evidence — run-based, before/after, both engines

### 4a. `simple test` cannot be used as evidence for this pass — proved, not inferred

`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:86` (the
self-hosted test runner every `bin/simple test` invocation uses):

```
env_set("SIMPLE_EXECUTION_MODE", "interpret")
```

with the adjacent comment:

> Child `run <file>` must execute in interpreter mode to load BDD test
> intrinsics (`describe`/`it`/`expect`). Without this, `simple test
> --mode=interpreter` can still dispatch a child in compile mode,
> producing parse errors + zero evidence.

(`test_runner_single.spl:168` has the identical override for the other test
entry point.) This unconditionally overwrites `SIMPLE_EXECUTION_MODE` before
every spec file runs, regardless of what the caller set. **No `.spl` spec,
however written, can exercise the Cranelift JIT path or this fix** — this
matches the sibling lane's independent finding for the `.to_i64()` bug (same
memory reference, final paragraph: the pinned spec "passes 4/4 identically
under plain `simple test` AND under `simple test` with
`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1`"). This document does not
land a spec claiming to cover the JIT path, and any reader of
`negative_step_slice_spec.spl`-style specs elsewhere in this campaign should
apply the same caveat: a `describe`/`it` spec is `simple test` evidence for
the *interpreter* only.

### 4b. `simple run` transcripts — before/after, both tagged rows

**IMPORTANT — deployed-binary caveat (per coordinator, verify before trusting
any number below):** the deployed `bin/simple` had **zero LLVM codegen**
from 2026-07-29 ~06:00 until a fresh, canonical, LLVM-linked build (154MB,
617 `llvm::` strings) was redeployed today. All runs below use a
freshly-built Rust-seed candidate binary from this pass's own worktree, not
the deployed `bin/simple` — this caveat does not change the validity of
this pass's own build/probe cycle, but is recorded here per instruction so
a future reader re-checks any *other* number that came from the deployed
binary during the affected window.

Built two real binaries from this pass's own worktree: `simple_jitstrict_before` (this pass's `exec_core.rs` edit reverted via
targeted `git stash`, everything else identical) and `simple_jitstrict_after` (this pass's fix applied). Both freshly compiled
(`cargo build --release --bin simple`, exit 0, no new warnings). Ran every fixture below directly against both, both engines/flags,
raw exit code captured without a pipe.

**Fixture A** — `bootstrap_hir_type_from_tag(3)` called as a function. As §0 explains, this hits row 7
(`first_unresolved_import`), not row 2 — included to show the boundary precisely:

```simple
fn main():
    val x = bootstrap_hir_type_from_tag(3)
    print(x)
```

| Run | Before this fix | After this fix |
|---|---|---|
| strict unset | exit 1, `[jit-fallback] unresolved external symbol '...'` + `[INFO] JIT compilation failed, falling back...` + interpreter's own `error[E1002]: function ... not found` (the function genuinely doesn't exist, so the interpreter fallback *also* fails — not a JIT-vs-interpreter divergence) | **byte-identical** |
| `SIMPLE_JIT_STRICT=1` | exit 1, `error: ... SIMPLE_JIT_STRICT: unresolved external symbol '...' would NULL-jump in JIT; refusing to fall back` (row 7 was already tagged since part 1) | **byte-identical** — confirms this pass did not disturb row 7 |

**Fixture B** — `gpu.barrier(1)` (`barrier()` takes no arguments; HIR's SIMD lowering rejects it, `hir/lower/expr/simd.rs:112`,
`Unsupported` variant, **not** gated by `lenient_types`). This is the one that actually demonstrates rows 2-3's fix, since the
`gpu.barrier` construct is unsupported in the plain interpreter too (so exit code stays 1 throughout) — the load-bearing signal is
which lines print, i.e. whether the interpreter fallback runs at all:

```simple
fn main():
    gpu.barrier(1)
```

| Run | Before this fix | After this fix |
|---|---|---|
| strict unset | exit 1 — `[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unsupported feature: gpu.barrier() takes no arguments` then `error: semantic: variable `gpu` not found` (interpreter ran, also failed) | exit 1 — **now also prints** `[jit-fallback] HIR lowering error: Unsupported feature: ...: whole module dropped to the interpreter ... Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.` ahead of the same two lines — new loud marker, same fallback behavior (default unchanged) |
| `SIMPLE_JIT_STRICT=1` | exit 1 — **identical output to the unset row above**: `[INFO] JIT compilation failed...` then `variable gpu not found` — **strict mode caught nothing; the interpreter fallback ran anyway**, the exact fail-open shape this pass exists to close | exit 1 — **one line only**: `error: SIMPLE_JIT_STRICT: HIR lowering error: Unsupported feature: gpu.barrier() takes no arguments; refusing to fall back to the interpreter`. The `[INFO] JIT compilation failed` line and the interpreter's `variable gpu not found` line are **both gone** — proof the interpreter fallback did not run |

The before/after delta that matters is not the exit code (1 in every cell, since this construct is invalid everywhere) but the
**control flow**: before this fix, `SIMPLE_JIT_STRICT=1` and strict-unset produce line-for-line identical output for this error
class (strict caught nothing extra); after this fix, strict mode suppresses the interpreter fallback entirely and terminates on
its own tagged error, while strict-unset stays byte-for-byte the same as before except for the added `[jit-fallback]` marker line.

Row 7 (unresolved import, the part-1 fix) re-verified unaffected by this pass's edit via Fixture A above — byte-identical
before/after in both strict settings.

Raw probe fixtures: `/tmp/.../scratchpad/probe_hir_unknown_var.spl` (Fixture A), `/tmp/.../scratchpad/probe_lower_unsupported.spl`
(Fixture B). Candidate binaries and build logs likewise scratch, not committed — same convention as part 1's own evidence section.

## 5. Summary

- Fixed: rows 2-3 (HIR/MIR lowering errors) now hard-fail under
  `SIMPLE_JIT_STRICT=1`, matching the tag convention row 7 established.
- Explicitly NOT fixed, by design, unchanged from part 1: rows 4-6, 8-9.
- Cannot ever be fixed by strict mode: row 10 (silent miscompiles). This is
  the load-bearing fact of this document — read §3 before trusting a clean
  strict-mode run as a correctness signal.
- No spec can serve as evidence for any of the above; only `simple run`
  transcripts can, because `simple test` forces interpreter mode
  unconditionally (§4a).

## Re-verified 2026-08-17 (worker s3_rust_other) — LIVE, matching the doc

Strict plumbing is present: `driver/src/exec_core.rs:1357` (unresolved-import
tag), `:1369` (paren-less accessor), generic helper `:1376-1379`
(`SIMPLE_JIT_STRICT` read, `is_some_and(|v| v != "0")`), consumed at
`exec_core.rs:955` (`jit_err.contains("SIMPLE_JIT_STRICT:")`); second reader at
`compiler/src/codegen/jit.rs:173-175`. The empty-let-pattern path the doc names
is at `hir/lower/stmt_lowering.rs:199`/`:206` — `} else if self.lenient_types {`
=> `TypeId::ANY`. It returns no `Err`, so no strict reader can ever observe it:
it fails open by construction, not by omission. Confirms the doc; no fix made.
