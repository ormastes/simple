# Native string interpolation of an array/dict slot renders empty text

**Filed:** 2026-11-26 (aarch64 native lane, worktree simple-bug-arm64-native-20261126)
**Status:** verified (2026-11-26) — fixed in `coerce_concat_operand`; spec `test/01_unit/compiler/mir/interpolation_array_render_spec.spl` green
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

## Fix and verification (2026-11-26)

`coerce_concat_operand` now sends a local through `rt_to_string` when it is
in `runtime_array_locals` or has an `Array`/`Dict` MIR type. This is the same
formatter `lower_bootstrap_print_call` uses for `print xs`. The array-handle
check runs before the scalar dispatch.

**Spec.** `interpolation_array_render_spec.spl` on the 11-26 seed: 4/4 pass
(it was 3 failed + 1 control passed before the fix). The in-development tag
is removed.

**Native.** Two Stage 2 compilers were built and admitted on this aarch64
host, one at each side of the change, with the same recipe
(`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --backend=cranelift`,
`COMPILER_BUILD_TIMEOUT_SECONDS=900`). Both compiled 1620 modules with 0
failed, and `stage2-sanity: pass` on both `SIMPLE_BOOTSTRAP` legs.

- base, 76892f19a3a: sha256 `567541f4ffd021a1...`
- fix, 880137c6f3e: sha256 `a0af3835012ec5f3...`

`test/fixtures/native_interpolation_array_text/main.spl`, native-built with
`--entry-closure` and diffed against the seed interpreter:

| Stage 2 | cranelift | llvm |
|---|---|---|
| base | DIFF (`interp=`, `s_len=0`, ...) | DIFF |
| fix | identical | identical |

On the fix compiler these probes are also identical to the interpreter on
both backends: the 2026-09-05 silent-wrong-values reproducer (now fully
equal, including `ys=[2, 4, 6]` and `xs=[1, 2, 3]`), `print` of int, text,
dict and f64 arrays, f64 arithmetic, mixed int/float, and `len` on text and
arrays. `d.size()` is still refused at build time.

**Compile cost and code size** (A/B, base vs fix, alternated run order). The
host was shared at load average ~30, so wall time is not usable; the figures
below are user+sys CPU from `/usr/bin/time`.

| program | backend | rounds | base CPU s (median) | fix CPU s (median) | object/binary/.text | max RSS |
|---|---|---|---|---|---|---|
| `native_if_val_presence` (500 lines) | llvm | 5 | 7.1 | 6.3 | byte-identical | within 0.2% |
| `native_if_val_presence` | cranelift | 5 | 6.3 | 6.8 | byte-identical | within 0.7% |
| `src/app/hash/main.spl` (92 modules) | llvm | 2 | 310.2 / 253.4 | 307.5 / 287.0 | byte-identical (obj 2,053,024 B) | within 0.2% |

Within each arm, round-to-round spread (up to 55% on cranelift base) is far
larger than any base/fix difference, and the sign flips between backends. No
regression is resolvable at this host load; generated code is unchanged for
programs without array or dict interpolation. The change itself adds one
dict lookup and one type lookup per non-text interpolation slot during MIR
lowering.

**Pre-existing, unrelated.** `struct_text_field_interpolation_source_spec`
(2 failed) and `scalar_compound_reassign_not_array_merge_spec` (1 failed)
fail identically with and without the fix.

**Rebase note.** After the native runs, the fix commit (880137c6f3e) was
rebased onto origin/release/1.0.0 b50fa563c68, 76 commits later. The only
upstream edit to `expr_dispatch.spl` in that range is at ~line 9493, outside
`coerce_concat_operand`. The MIR spec was rerun at the rebased tip: 4/4
pass. The native Stage 2 evidence above is from the pre-rebase commit.
