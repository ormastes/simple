# Phase 2 lowers `text.byte_at(i).to_i64()` as text-to-int parsing (2026-11-23)

Status: FIXED-IN-SOURCE (takes effect from the next compiler built from this source;
already-built Phase 2/3 binaries keep the defect)
Severity: blocks Windows Phase 3 admission (every cold-init probe fails)
Compiler: fresh admitted Phase 2 `stage2-admitted/simple.exe`
(sha256 `baa8d0d5bfda0aa8f5b18292c2b68dfba0115f1045fc571e1c0228c9e90dc030`, built from `8dae652711e`)

## Symptom

A Phase 3 compiler built by this Phase 2 fails every admission probe that cold-initializes
the package index (scv-prime, p2_add, struct receiver):

```
[first-compile-error] frozen cold entry rejected: root-not-canonical
```

## Root cause

`phase_compatibility_windows_spelling_io_v1`
(`src/compiler/00.common/cache/phase_compatibility_path_io.spl:77`) does

```
val drive = path.byte_at(0).to_i64()
```

Phase 2 routes `.to_i64()` on the `byte_at` result through the TEXT method table
(`method_calls_literals.spl:5250`, `case "to_int" | "to_i64": "rt_string_to_int_lenient"`).
The byte is boxed into a text and parsed, so `'C'` becomes `0`. The drive-letter check
then fails, and `phase_compatibility_canonical_directory_io_v1` rejects at `:157` with
`root-not-canonical`.

## Evidence

- cdb attached to the `native_build_worker` child of `simple-p3` during p2_add. The root is
  `C:/dev/simple-release-boot-p3-20261122/build/bootstrap/pinned-src/pinned-8dae652711e9/build/scv/snapshots/scv-revision-v2-d62d6401…7001e`,
  `spelling_equivalent_v1` returned 1, and `windows_spelling_io_v1` returned 0 for this valid path.
- `uf /c` of `phase_compatibility_windows_spelling_io_v1` in the Phase 3 binary shows the calls
  `_simple_rt_string_byte_at` -> `rt_string_new` -> `rt_string_to_int_lenient`.
- `llvm-nm -u` on the module object: the original imports `rt_string_to_int_lenient`; after
  rewriting to `as i64` it does not.
- Minimal repro compiled by Phase 2 (hello-sanity flags, `--backend llvm --runtime-bundle core-c-bootstrap --mode one-binary`):

  | form | `"C:/x"[0]` | `"C:/x"[2]` |
  |---|---|---|
  | `s.byte_at(i).to_i64()` | **0** | **0** |
  | `s.byte_at(i) as i64` | 67 | 47 |
  | `val b: u8 = s.byte_at(i); b.to_i64()` | 67 | 47 |

  `.to_u8()`, `.to_u64()` and `.to_i32()` on `byte_at(i)` are correct (67); only `to_i64`
  (and presumably `to_int`) collide with the text table.

## Affected sites in the Phase 3 closure

- `src/compiler/00.common/cache/phase_compatibility_path_io.spl:77, 89, 99`
- `src/compiler/50.mir/loop_module_shape_owner_v1.spl:592`

Outside the closure: `src/os/kernel/loader/smf.spl` (uses `_smf_byte_at`, not checked).

## Workaround

Use the house idiom `byte_at(i) as i64`. It was applied in the private tree
`/c/dev/simple-p3-w22` to the four sites above, and only those two modules were recompiled.

## Upstream

`origin/release/1.0.0` (`a80de9efd73`) leaves the text-dispatch gate in
`method_calls_literals.spl` unchanged and still has the source sites. No fix was found,
but this was not verified by a build. Fix in MIR: `to_i64` / `to_int` must not take the
text table when the receiver type is `u8` (the `byte_at` return).

## Fix (2026-11-23)

Why only `to_i64` / `to_int` broke: the erased-receiver text-builtin admission in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (`erased_text_shape`,
~line 3445) admits a receiver with no HIR type when the method name is in
`primitive_text_method_shape`. `to_i64` and `to_int` are in that set (text parse aliases);
`to_u8`, `to_u64` and `to_i32` are not, so they always reached the numeric conversion arm.
The arm rejects a receiver only when it is a proven numeric scalar
(`local_is_proven_numeric_scalar`) or a proven numeric expression
(`builtin_numeric_expr_kind`). The `byte_at` lowering arm (~line 5985) returned a raw
`i64` local with no recorded HIR type, and `builtin_numeric_expr_kind` had no `byte_at`
case, so neither proof held.

Change:

- `method_calls_literals.spl` `byte_at` arm: record `i64` as the HIR type of the result
  local. That makes it a proven numeric scalar.
- `builtin_method_extras.spl` `builtin_numeric_expr_kind`: `byte_at(i)` on a declared
  text receiver is a proven signed integer. This also covers arithmetic over it and
  untyped `val b = s.byte_at(i)` locals.

Specs: `test/01_unit/compiler/50.mir/byte_at_to_i64_numeric_receiver_spec.spl` has two
reproducers (chained `byte_at(0).to_i64()` and `byte_at(i).to_int()`), two generalisation
cases (an untyped bound local, and an arithmetic receiver), and a control (`text.to_i64()`
still parses). On the old source 4 of 5 fail and the control passes. On the fixed source
5 of 5 pass.

The source workaround sites listed above were left alone. The compiler fix covers them.
