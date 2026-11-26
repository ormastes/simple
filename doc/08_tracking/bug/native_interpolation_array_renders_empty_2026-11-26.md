# Native string interpolation of an array/dict slot renders empty text

**Filed:** 2026-11-26 (aarch64 native lane, worktree simple-bug-arm64-native-20261126)
**Status:** open — red spec `test/01_unit/compiler/mir/interpolation_array_render_spec.spl` (`@tag:in-development`)
**Severity:** P2 — silent wrong value, exit 0, no diagnostic
**Area:** pure-Simple MIR lowering (`src/compiler/50.mir`), arch-neutral

## Reproduction

Fixture: `test/fixtures/native_interpolation_array_text/main.spl` (expected stdout in its header).

Compiler: admitted Stage 2 (sha256 `53e9e2e7513658f1...`, pinned 4995f23e7ccd = release 57e92cb68fc7 + docs/tests) built by
`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --backend=cranelift`
(1620 modules compiled, 0 failed, sanity pass). Also reproduces on the unadmitted 57e92cb68fc7 build (`a973f9bbfdc5ef43`).

```
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_GO_TO_END=1 SIMPLE_FILE_WORKERS=0 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 \
  <stage2> native-build main.spl --backend=<cranelift|llvm> --entry-closure --cache-dir c -o out && ./out
```

| line | seed (`simple run`) | stage2 native (cranelift and llvm) |
|---|---|---|
| `"interp={xs}"` | `interp=[1, 2, 3]` | `interp=` |
| `"{xs}".len()` | `9` | `0` |
| `"{xs}"` returned from a fn | `fn=[1, 2, 3]` | `fn=` |
| `"{ts}"` (`[text]`) | `text_arr=[a, b]` | `text_arr=` |
| pushed array | `pushed=[4]` | `pushed=` |
| `"{n}"` (i64, control) | `int=5` | `int=5` |

Also reproduces on the 2026-11-22 integ27 Stage 2 (cd29cfa8b64c). The
2026-09-05 record `stage2_native_codegen_silent_wrong_values_aarch64_2026-09-05.md`
printed `xs=[1, 2, 3]` correctly, so this is a regression.

## Root cause

`lower_string_interpolation` (`_MirLoweringExpr/expr_dispatch.spl`) sends each
non-text slot through `coerce_concat_operand`, which renders scalars
(`rt_raw_*_to_string`), `Any`/type params (`rt_value_to_string`), tuples and
chars, and otherwise returns the operand unchanged. An array or dict handle
therefore reaches `rt_strcat_tagged` raw; its text view of a non-string word
is empty. Disassembly of `main.show` has `rt_string_new` + `rt_strcat_tagged`
and no render call.

Not aarch64-specific: the x86_64 object of the same fixture
(`native-build --target=x86_64-unknown-linux-gnu`, object emitted before the
cross link refused) has the same relocation sequence in `main.show`
(`rt_string_new`, `rt_strcat_tagged`, no `rt_to_string`).

The bare `print xs` path already handles this: `lower_bootstrap_print_call`
(`switch_operators_calls.spl`) routes `runtime_array_locals` and
Tuple/Dict/Struct/Enum through `rt_to_string`. The likely fix is the same arm
in `coerce_concat_operand`. Not fixed in this lane (its mandate was
aarch64-only codegen); handed to the coordinator.

## Red evidence

`<seed 11-26> test test/01_unit/compiler/mir/interpolation_array_render_spec.spl`:
3 failed (array flat path, array typed path, dict), 1 passed (i64 control
keeps `rt_raw_i64_to_string`).
