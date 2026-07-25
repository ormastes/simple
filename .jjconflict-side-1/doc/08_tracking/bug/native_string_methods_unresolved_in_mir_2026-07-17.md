# Native path: `.parse_f64()` and `.to_upper()` unresolved in MIR lowering

**Date:** 2026-07-17
**Severity:** Medium (loud build failure, not silent-wrong; but a real
functionality gap vs. the oracle)
**Status:** SOURCE FIXED (current Cranelift execution pending)
**Task:** #178 native text interpolation + string ops verification round 2 (lane S47)

## Symptom 1 — `.parse_f64()`

```simple
fn main():
    val a = "3.14".parse_f64()
    print "F1:{a}|END"
```

- Oracle: `F1:3.139999999999997|END` (works; the trailing-digits artifact is
  the oracle's own float-parse rounding behavior, not a bug — just the
  baseline to match).
- Native (`native-build`, `SIMPLE_BOOTSTRAP` unset): fails to build:
  ```
  [mir-lower] WARNING: unresolved method call 'parse_f64' lowered to const-0 placeholder (silent-null risk, Task #145)
  [ERROR] MIR error: MIR lowering error: unresolved method call: parse_f64
  error: MIR lowering error: unresolved method call: parse_f64
  ```

`.parse_int()`/free-function `int(...)` both work correctly natively
(regression-checked in the same sweep, no divergence there).

## Symptom 2 — `.to_upper()`

```simple
fn main():
    val s = "Hello"
    print "UP:{s.to_upper()}|END"
```

- Native (`native-build`, `SIMPLE_BOOTSTRAP` unset): fails to build with the
  identical shape:
  ```
  [mir-lower] WARNING: unresolved method call 'to_upper' lowered to const-0 placeholder (silent-null risk, Task #145)
  [ERROR] MIR error: MIR lowering error: unresolved method call: to_upper
  error: MIR lowering error: unresolved method call: to_upper
  ```

Confirmed via source read: `src/compiler/50.mir/_MirLoweringExpr/*.spl`
(the native MIR-lowering layer used by `native-build`) has no `to_upper`/
`upper` dispatch arm anywhere, unlike `to_lower`/`lower`, which are handled
alongside `trim`/`replace`/`split` (`method_calls_literals.spl` ~line 1736).
`to_upper` **is** handled in the older `cg_expr.spl` codegen path and in the
tree-walking interpreter (`eval_methods.spl` line 452), which is why it is
absent specifically from the MIR/native-build path, not from the language as
a whole.

**Note on the oracle's own `.to_upper()`:** re-verified in isolation
(`"Hello World".to_upper()` on `bin/simple run`) — the oracle prints `Hello
World` unchanged, i.e. the seed's own `to_upper()` is a no-op. This looks like
a pre-existing limitation of the feature-incomplete bootstrap seed itself,
not a native regression, so no oracle-side value comparison is possible for
this method; only "does native-build succeed at all" was checked here. Not
filed separately — the seed is bootstrap-only per repo convention and this
lane's mandate is native-vs-oracle parity for the native (pure-Simple) path.

Both failures are **loud** (correctly so, per the existing Task #145
"silent-null risk" guard converting unresolved calls into hard errors rather
than silently emitting a placeholder) — filed as functionality gaps, not
silent-wrong-answer bugs.

Note: this is a different symptom from the older, already-tracked
`pure_simple_text_split_lines_missing_2026-07-13.md`-style "seed oracle lacks
a recently-landed native feature" pattern — here it is the **reverse**: the
oracle has the feature (or a no-op stand-in, for `to_upper`), native's MIR
lowering does not resolve the call at all.

## Expected

`.parse_f64()` should resolve to a real runtime float-parse call
(`rt_string_to_f64`/similar) in native MIR lowering, matching the oracle's
behavior including its rounding characteristics. `.to_upper()` should resolve
to `rt_string_to_upper` (already declared for the LLVM backend in
`src/compiler/70.backend/backend/llvm_lib_translate.spl` line 396 — the
runtime symbol exists, only the MIR dispatch arm is missing).

## Suggested direction

Add `method == "parse_f64"` and `method == "to_upper"` handling arms in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, alongside
the existing `find`/`replace`/`trim`/`lower`/`to_lower` dispatch table
(~line 1777), calling `rt_raw_f64_to_string`'s parse-side counterpart for
`parse_f64` and the already-declared `rt_string_to_upper` for `to_upper` —
mirroring exactly how `to_lower` is already wired in the same arm.

## Verification

- Reproduced on worktree `/home/ormastes/dev/wt_r_find_infer` at tip
  `ffc0c360ba4` (fetched 2026-07-17), using
  `env -u SIMPLE_BOOTSTRAP bin/simple run` (oracle) and
  `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build`
  (native).

## Resolution update (2026-07-19)

The shared MIR dispatch and hosted LLVM runtime were already fixed. Cranelift's
remaining failure was an ABI mismatch: its generic external-call fallback
declared `rt_string_parse_f64` as i64-to-i64 even though MIR expects a raw f64
result. The Pure runtime now owns `rt_string_parse_f64(i64) -> f64`, and the
Cranelift adapter uses a dedicated i64-to-f64 import signature before local or
generic call lookup. Cranelift function definitions, indirect calls, and
runtime imports now request the platform calling convention rather than
hardcoding SystemV, so native-hosted Windows uses its required ABI too.

The existing C9 system fixture is now part of the strict LLVM/Cranelift hosted
matrix, the focused FreeBSD Cranelift selection, and AArch64/RISC-V64 Cranelift
QEMU execution. Source/ABI checks pass review; execution with a rebuilt current
Pure Stage3 remains pending.

## Nullable ABI correction (2026-07-24)

The raw-f64 shortcut was still semantically wrong: invalid input and valid
zero both produced `0.0`, and `strtod` accepted trailing junk. MIR now calls
the existing nullable tagged `rt_string_to_float` owner, records
`Optional<f64>` metadata, and lets `unwrap`/`unwrap_or` perform the established
runtime-value decode. Hosted C and pure-Simple runtimes both require complete
input consumption and return nil on failure; the dedicated raw-f64 runtime and
Cranelift import ABI were removed.

C9 now checks valid nonzero, valid zero, invalid text, and trailing junk while
retaining the existing result `42`. Rebuilt LLVM/Cranelift execution remains
pending.
