# Importing `std.nogc_sync_mut.io_runtime` fails native-build on a borrow-checker error

**Status:** FIXED (2026-08-24) in `9e3eb1adccd` — TWO sequential defects, both fixed. See "Resolution" below.
**Still blocked downstream by a THIRD, separate defect:** `doc/08_tracking/bug/llvm_backend_no_result_match_semantic_2026-08-24.md`
**Was:** Open — blocker for every `native-build` of a module importing `io_runtime`
**Observed:** 2026-08-24
**Area:** borrow checker / HIR import dependency resolution

## Relationship to the `unsafe` defect (read this first)

Split out of `unsafe_expression_import_lowering_2026-08-24.md`. That record
claimed "**every** `native-build` on `origin/main` is blocked" by the lexical
`unsafe` defect, using an `io_runtime`-importing control fixture as evidence.
That attribution was wrong on two counts:

- The `unsafe` defect was a **stale seed binary**, and is resolved. See the
  retraction section of that record.
- The control fixture still fails with a freshly built seed, but on **this**
  defect, which has nothing to do with `unsafe`. All three `unsafe`-defect
  signatures now count zero on this fixture: `function 'unsafe' not found` = 0,
  `unresolved identifier 'ffi'` = 0, `env_get ... body compilation failed` = 0.

So this — not `unsafe` — is what currently blocks `io_runtime` importers.
Standalone native-builds that do not import `io_runtime` succeed.

## Reproduction

Seed: `cargo build --release --bin simple` at `origin/main` (BUILD_RC=0),
binary size 60513440, mtime 2026-08-24 18:12. No source modifications.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ "$SEED" native-build control.spl -o control.bin
$ NB_RC=$?      # read directly, not through a pipe
NB_RC=1
```

## Verbatim errors

```text
error: 37:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
error: 43:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
error: 54:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
error: 66:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
error: 73:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
```

Accompanied by unresolved import-dependency origins, which may be the same root
cause or a second defect — unseparated as yet:

```text
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime dependency=Option: no declaration, re-export hop, or explicit import of this name in the owner; a later `unresolved type: Option` will be reported against an importing module instead
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime dependency=Result: no declaration, re-export hop, or explicit import of this name in the owner; a later `unresolved type: Result` will be reported against an importing module instead
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops   dependency=Result: ...
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops   dependency=Option: ...
```

Note the diagnostic's own wording: the unresolved origin is deliberately
deferred and "reported against an importing module instead", which is why the
failure surfaces in the trivial caller rather than in `io_runtime` itself.

## Required next evidence

- Determine whether the `borrow of local(13)` errors and the unresolved
  `Option`/`Result` dependency origins share a root cause, or are two defects.
- Identify which `io_runtime` declarations the line numbers (37, 43, 54, 66, 73)
  refer to — they are reported without a file path, which is itself a
  diagnostic-quality gap worth fixing.
- A regression gate should be behavioural (native-build a fixture importing
  `io_runtime` and require NB_RC=0), following the pattern of
  `scripts/check/check-unsafe-block-native-build.shs`.

## Not this defect

Lexical `unsafe` in either form. Both the statement/block and the
expression/value form native-build and execute correctly, pinned by
`scripts/check/check-unsafe-block-native-build.shs` (`PASS — 3 case(s) checked`).


---

# Resolution (2026-08-24)

This record described ONE defect. Measurement found **two, in sequence**, and
the record's framing was wrong on two further counts. Both are fixed.

## Correction 1 — the blast radius was never io_runtime-specific

`io_runtime` was a symptom, not the scope. Measured on a freshly built seed at
`origin/main` (`cargo build --release --bin simple`, BUILD_RC=0), with exit
codes read DIRECTLY into a variable on the line after each command:

| fixture | pre-fix | post-fix |
|---|---|---|
| bare `fn main(): print(...)`, no imports | RC=0 | RC=0 |
| local two-file import (no stdlib) | RC=0 | RC=0 |
| `use std.common.json` | RC=0 | RC=0 |
| `use std.common.math` | RC=1 | **RC=0, binary runs** |
| `use std.nogc_sync_mut.io.signal_stubs` | RC=1 | **RC=0, binary runs** |
| `use std.common.text` | RC=1 | RC=1 (different defect, see below) |
| `use std.nogc_sync_mut.fs` | RC=1 | RC=1 (different defect) |
| `use std.nogc_sync_mut.io_runtime` | RC=1 | RC=1 (different defect) |

## Correction 2 — the recorded borrow signature was MASKED, not primary

On a freshly built seed the reported `borrow of local(13)` signature counted
**zero**. The first failure was a different, earlier one:

```text
error: semantic: variable `type_` not found
```

Only after defect 1 was fixed did the borrow errors appear (19 of them), with
the recorded text verbatim. So the original signature was real but sat behind
an earlier blocker. Both are now fixed.

## Defect 1 — `if val` in EXPRESSION position never bound its name (seed interpreter)

`Expr::If` carries a `let_pattern: Option<Pattern>` field
(`parser/src/.../expr.rs:556`). The EXPRESSION-position evaluator,
`compiler/src/interpreter/expr/control.rs`, destructured it away with `..`:

```rust
Expr::If { condition, then_branch, else_branch, .. } => {
```

It then chose the branch from the condition's TRUTHINESS. So
`val x = if val v = e: ... else: ...` entered the then-branch with `v` **never
bound**, and every read of `v` failed with ``variable `v` not found``. The
statement form (`exec_if_core`, `interpreter_control.rs`) has always done this
correctly via `optional_let_binding`.

The compiler's own MIR lowering uses exactly that shape at
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1794`:

```
val has_base_mir_type = if val type_ = self.builder.local_type(base_local):
    base_mir_type = type_
```

which is why the error names `type_`. Localized by an env-gated provenance
probe added in the same change (see "Diagnostic added"), which printed:

```text
[undefined-var] name=type_ call_stack_top=["lower_index_expr", "lower_index_expr_from_hir", ...]
```

and by an in-place `.spl` bisect proving the branch was ENTERED (probe-A fired)
but died on the first read of `type_` (probe-B never fired).

**Fix:** `compiler/src/interpreter/expr/control.rs` now destructures
`let_pattern` and delegates presence + binding to `optional_let_binding` — the
same helper the statement form uses — so both forms agree, including on the
"0 is falsy" landmine (`Some(0)` is PRESENT and takes the then-branch).

## Defect 2 — the Return borrow check could never pass a `Ref`-containing function

`src/compiler/55.borrow/borrow_check/` never ends a borrow:

- `end_borrow` (`borrow_graph.spl:642`) has **zero callers**.
- `propagate_borrows` copies every borrow forward unconditionally — its own
  comment says `(simplified: copy all borrows)`.
- `check_terminator`'s `Return` arm took a `liveness: LivenessResult` argument
  and **never read it**.
- `LivenessAnalysis.record_use` / `record_def` also have **zero callers**, so
  `live_in`/`live_out` were empty for every block — the liveness it was handed
  was starved anyway.

So any function containing any `MirInstKind.Ref` was rejected at EVERY return.
A probe identified the offender as
`std.nogc_sync_mut.io.process_ops::process_read_stdout_result`, whose borrow is
an **out-parameter**:

```
val chunk = _process_read_stdout_checked_raw(pid, &mut status)
```

`&mut status` is consumed by the call and never escapes; the function has six
returns, matching the reported points. This is a **checker false positive**,
not invalid code — the two require opposite fixes and the distinction was
established by measurement, not assumption.

**Fix:** the `Ref` instruction's `dest` (the reference temp), previously
discarded in `mod.spl`, is now recorded; `Ret` operands are recorded as
returned locals; and the Return arm reports only when the borrow's reference
actually escapes via the return value.

**Accepted limitation, stated not hidden** (documented on
`borrow_reference_escapes`): escape via a global or field store is not
modelled, and copy-propagation (`val r = ref_temp; return r`) is not followed.
Both make the check UNDER-report. That is deliberate — the previous behaviour
reported unconditionally and therefore discriminated nothing.

## Still open — a THIRD, separate defect (out of scope here)

`io_runtime` still does not native-build, now failing further down the
pipeline in the backend:

```text
error: E-BACKEND-LLVM-INST-ResultMatchSemantic: LLVM backend does not lower ResultMatchSemantic
```

Now filed separately as
`doc/08_tracking/bug/llvm_backend_no_result_match_semantic_2026-08-24.md`.
`std.common.text` and `std.nogc_sync_mut.fs` likewise now fail on unrelated
MIR-lowering gaps (`unresolved method call: index_of`, `undefined variable
Dir`). These are distinct defects and are NOT this record.

## The `Option`/`Result` dep-origin question — answered: non-fatal noise

`[hir-callable-dep-origin-unresolved] owner=... dependency=Option/Result` is
emitted on builds that **succeed** as well as ones that fail. It was never the
blocker. No change made.

## Diagnostic added

The interpreter reported only the NAME of an unresolved identifier — no file,
line, or enclosing function — which is what made this unlocalizable. A
level-gated probe (default OFF; `SIMPLE_DEBUG_UNDEFINED_VAR=1`, or the existing
`SIMPLE_BOOTSTRAP_DIAG=1`) now dumps the interpreter call stack and the names
in scope. Retained per the logging-retention policy.

## Regression gate

`scripts/check/check-ifval-expr-binding-and-outparam-borrow.shs`
— `--selftest` FIRST and FATAL (5 fixtures), verdict LAST on stdout.

```text
$ sh scripts/check/check-ifval-expr-binding-and-outparam-borrow.shs --selftest
PASS — 5 selftest fixture(s) checked
$ sh scripts/check/check-ifval-expr-binding-and-outparam-borrow.shs
PASS — 5 case(s) checked
FINAL_GATE_RC=0
```

Mutation-tested in both directions:

| mutation | verdict |
|---|---|
| remove the `borrow_reference_escapes` gate in `nll.spl` | `FAIL — 5 case(s) checked, offender(s): io_runtime-outparam-borrow-at-return` (rc=1) |
| drop the `env.insert` binding in `control.rs` | `FAIL — 5 case(s) checked, offender(s): signal-stubs-native-build(rc=1) io_runtime-type_-unbound` (rc=1) |

Case D asserts SIGNATURE ABSENCE rather than rc=0, because the third defect
above still blocks that module; asserting rc=0 there would make the gate untrue.

## Note for whoever touches the gate's fixtures

An `i64` Option payload binds left-shifted by 3 under the seed (`Some(40)`
reads back as `320`). That is a **separate, pre-existing** tagging defect — it
reproduces identically in the STATEMENT form — so the gate uses a `text`
payload deliberately. Do not "fix" the gate by encoding the shifted value.
