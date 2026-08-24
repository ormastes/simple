# `a[i]` on a typed array loses the element type on the native lane (2026-08-24)

**Date:** 2026-08-24
**Status:** OPEN — reproduced, localized to named lowering sites, NOT fixed
**Severity:** Critical — silent wrong values, and it turns every Stage-2 compile
error into an undiagnosable SIGSEGV
**Platform:** x86_64-unknown-linux-gnu, `--backend=cranelift`
**Lane:** private worktree at `73331690322`, `git status --porcelain` = 0 at
creation; seed built in-lane (`cargo build --release --bin simple`, 3m15s)

## Reproducer — 7 lines

```
fn main():
    var a: [text] = []
    a.push("BOOM")
    val s: text = a[0]
    print "idx={s}"
    print "direct={a[0]}"
    print "len={a.len()}"
```

| line | interpreter (`bin/simple run`) | native (`bin/simple native-build`) |
|---|---|---|
| `idx={s}` | `BOOM` | `RTS` |
| `direct={a[0]}` | `BOOM` | `94900188322657` |
| `len={a.len()}` | `1` | `1` |

`.len()` is correct, so the array is intact. Only the ELEMENT READ is wrong.
Exit codes were read directly into variables on the line after each command,
never through a pipe: `RC_INTERP=0`, `RC_BUILD=0`, `RC_RUN=0`. The build is
clean — this is silent wrong data, not a compile failure.

## Scope — every element type except i64

Measured with `scripts/check/check-native-array-element-type.shs`:

```
i64: MATCH V=42
text: DIVERGE interp=[V=BOOM] native=[V=104913387449185]
bool: DIVERGE interp=[V=true] native=[V=1]
f64: DIVERGE interp=[V=1.5] native=[V=0.0]
FAIL — 4 case(s) checked, 3 diverged: text bool f64
```

`f64` is the worst: `1.5` reads back as `0.0`, so this is DATA LOSS, not only a
rendering difference.

**Not an empty-literal inference artifact.** All four spellings fail
identically — `var a: [text] = []` then push, `var a: [text] = ["X"]`, an
inferred `val c = ["Z"]`, and an array received as a `[text]` parameter. Only
the element type matters, not how the array was formed.

## Why this is load-bearing for the bootstrap

`CompileContext.error_message_at` (`src/compiler/80.driver/driver_types.spl:1013`)
is exactly this shape:

```
fn error_message_at(index: i64) -> text:
    if index < 0 or index >= self.errors.len():
        return ""
    self.errors[index]
```

`self.errors` is a `[text]`, so under a Stage-2-compiled compiler that read
returns a garbage text handle. Consequence, measured: **a Stage-2 binary SEGVs
on a two-line hello world.**

```
$ ./stage2/simple native-build hello.spl --backend=cranelift -o /tmp/h
[ERROR] MIR error: E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED: retained module
        surface payload malformed at HIR entry (heap-typed payload word is 0 or
        in the zero page)
Segmentation fault (core dumped)          RC=139
```

gdb, on that exact crash:

```
Program received signal SIGSEGV, Segmentation fault.
0x0000000000e58bb3 in compiler__driver__driver_types__CompileContext_dot_error_message_at ()
#0  compiler__driver__driver_types__CompileContext_dot_error_message_at ()
#1  compiler__driver__driver_aot_pipeline__CompilerDriver_dot_aot_compile ()
#2  compiler__driver__driver_orchestration__CompilerDriver_dot_compile ()
#3  compiler.driver.driver.compiler_driver_run_compile ()
#4  app.cli.bootstrap_main.run_native_build_bootstrap ()

rdi 0x0     rax 0x0
=> mov 0xb0(%rax),%r10
```

Note the ORDER at `driver_aot_pipeline.spl:78-97`: `for err in self.ctx.errors:`
iterates the same field and prints the message SUCCESSFULLY, and
`self.ctx.error_count_value` (a scalar on the same object) reads correctly —
then `error_message_at(0)` faults. So the context is live; the indexed element
read is the broken step.

This is why Stage-2 failures present as bare SIGSEGVs with no diagnostic: the
compiler crashes while REPORTING the error it correctly detected.

## Root cause — named sites, from source

- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1656` `lower_index_expr`
  — result type starts at `var result_type = MirType.i64()` (`:1727`) and is
  refined only from sources that are erased for these cases.
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:848`
  `note_container_elem_type` — records **only** F64/F32, struct names and
  nested-array element types. Never `Str`, never `Bool`:
  ```
  if vt_disc == rt_enum_discriminant(MirTypeKind.F64) or vt_disc == rt_enum_discriminant(MirTypeKind.F32):
      self.runtime_elem_value_type[container.id] = vt
  ```
- The decoded element local is never passed to `remember_local_hir_type` or
  `mark_tagged_text_local`, so `local_is_str` (`:522`) is false and
  `coerce_concat_operand` (`:572`) falls through to `rt_raw_i64_to_string` —
  the same render-dispatch defect fixed for `Any` locals in `eaac3400b86`,
  still live for array elements.

**The correct model already exists in the tree.** `.first()`/`.last()`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4358-4461`)
resolves the element HIR type from `find_local_hir_type` then
`receiver_declared_type`, **fails closed to nil when unknown** (`:4392`), maps
`HirTypeKind.Str -> self.bootstrap_text_type()` (`:4397-4399`), and finishes
with `remember_local_hir_type(result_local.id, option_type, 2, 0)` (`:4461`).
The Index path should do the same.

Related but not identical, all pre-existing:
`untyped_list_element_read_seed_rootcause_2026-07-30.md`,
`pure_simple_untyped_list_element_read_unconditional_int_decode_segv_2026-08-08.md`,
`native_text_bracket_index_no_string_lowering_2026-07-17.md`,
`native_split_array_element_access_raw_handle_2026-07-17.md`.
None covers this exact shape (a declared `[text]`/`[bool]`/`[f64]` indexed read
diverging while `.len()` is correct).

## Gate

`scripts/check/check-native-array-element-type.shs` — `--selftest` runs FIRST
and is FATAL (5 fixtures, all exercising the comparator itself so it cannot
depend on the compiler under test being healthy); verdict is the LAST line on
stdout. `PASS — <n> case(s) checked, 0 diverged` exit 0 / `FAIL — ...` exit 1 /
`ERROR — nothing was checked (<reason>)` exit 2. A run that reached 0 cases is
ERROR, and a missing compiler is ERROR, never a pass (verified: exit 2 with
`SIMPLE_BIN=/nonexistent/simple`).

Landed **ADVISORY because it is honestly RED**: `FAIL — 4 case(s) checked,
3 diverged: text bool f64`. It discriminates rather than always failing — the
`i64` case MATCHes on the same run. Promote to MANDATORY when it goes green.

## NOT established

- Whether fixing this alone unblocks Stage 3. The Stage-3 self-host SEGV has a
  separate, independently measured escape point (see
  `stage3_n_modules_zero_segv_mir_lowering_x86_64_2026-08-24.md`), and the two
  have not been shown to be the same defect.
- Which of the two lowering gaps above is sufficient on its own.
