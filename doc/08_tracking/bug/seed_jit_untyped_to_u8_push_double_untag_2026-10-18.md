# Seed JIT: `.to_u8()` / push on an untyped (`Any`) value is mis-encoded (value >> 3)

Date: 2026-10-18. Found by: gzip hardening lane. Binary: Rust seed `bin/local/seed_simple`
(sha256 prefix 9c45d2bf601ab93e), default JIT mode. Interpreter mode is correct.

## Symptom
A gzip_compress_default + gzip_decompress round trip (any size, even 0 bytes)
printed `ok=0 same=false` under JIT and `ok=65536 same=true` under
`SIMPLE_EXECUTION_MODE=interpreter`.

## Minimal repro
`test/fixtures/compiler/seed_jit_untyped_any_tag_repro/main.spl`: pushing `v.to_u8()` into `var bytes = bs[0]` (untyped array
taken from an `[Any]` tuple) stores `99` as `12` (99 >> 3) under JIT; annotating
`var bytes: [u8] = bs[0]` gives 99. Same for `x.to_u8()` where `x` is an UNTYPED fn
parameter (`gzip_footer_create(crc32, size)`: footer bytes came out as value << 3).

## Root cause (our side)
Untyped params / `[Any]` tuple slots carry tagged values; JIT `to_u8()` + `push` on them
double-(un)tags. Not fixed in the seed; worked around in .spl with typed idioms:
- `header.spl`: `gzip_header_create(... timestamp: i64, extra_flags: i64, os_type: i64) -> [u8]`,
  `gzip_footer_create(crc32: i64, size: i64) -> [u8]`, `var header: [u8]`, `.to_u8()` pushes.
- `huffman.spl`: bitstream writer keeps its byte buffer as `[i64]` (`var bytes: [i64] = bs[0]`)
  and converts to `[u8]` once in `bitstream_finish`.

## Status
FIXED in the seed 2026-11-06 (branch `work/seed-jit-miscompiles-20261106`). The `.spl`
workarounds in `header.spl` / `huffman.spl` are no longer required by the seed but were
not reverted here.

Two seed defects, both in `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`:

1. **Bare push on an erased receiver stored a raw scalar.** `var bytes = bs[0]` is `Any`,
   so `bytes.push(x)` is emitted as a bare `MethodCallStatic "push"`, which codegen always
   routes to the tag-dispatched builtin `rt_push`
   (`codegen/instr/closures_structs.rs`, `is_bare_builtin_collection_method`). Only the
   typed-array path (`receiver_is_array`) boxed native scalars; the bare path passed the
   raw `99`, read back as a tagged word (`99 >> 3 == 12`). Fix: `box_method_args_for_any_params`
   boxes the single argument of a bare `push`/`append` via `box_arg_for_any_param`
   (no-op for already-tagged values).
2. **Numeric cast of a just-boxed erased value narrowed the tag word.**
   `(crc & 255).to_u8()` with an untyped `crc`: the `&` is computed raw, then `BoxInt`'d
   (HIR types it `Any`), then a bare `to_u8`. Codegen types every `BoxInt` dest as `I64`
   (`codegen/instr/body.rs:461`), so the erased-cast decode (`rt_any_to_int`, gated on an
   ANY/unknown vreg type, `closures_structs.rs:2136`) was skipped and the tagged word was
   reduced: footer bytes `(v << 3) & 0xff`. Fix: when the bare cast's receiver is a
   `BoxInt` in the current block, cast its raw source as `i64.<cast>` instead.

Evidence:
- Rust test `compiler/tests/erased_scalar_boundary_jit.rs`: before the fix
  `scalar_pushed_onto_erased_array_reads_back_unchanged` and
  `cast_of_arithmetic_on_untyped_param_is_not_tagged` FAIL; after, 3/3 pass.
- `SIMPLE_EXECUTION_MODE=jit`, old seed (2026-10-05) vs fixed seed:
  - `test/fixtures/compiler/seed_jit_untyped_any_tag_repro/main.spl`:
    `untyped=[[12]] typed=[[99]] i64=[[12]] rev=1279022294173220864` ->
    `untyped=[[99]] typed=[[99]] i64=[[99]] rev=142 rev2=142` (the `rev` half was the
    erased-arg class, already fixed by 6581807d48c);
  - `test/fixtures/compiler/seed_jit_miscompiles/erased_push_scalar.spl`:
    `u8=[12] i64=[<special:12>] footer=[192, 176]` -> `u8=[99] i64=[99] footer=[120, 86]`.
- `test/01_unit/lib/common/compress/gzip_spec.spl` on the fixed seed: 6/6 passed.
