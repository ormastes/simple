# hir_codec_required_functions_spec: 3 canonical-path examples RED while the canonical codec is gated

- Status: open (expected RED; unblock condition below)
- Spec: `test/01_unit/compiler/hir/hir_codec_required_functions_spec.spl`
- Gate: `src/compiler/20.hir/hir_codec.spl:71` `hir_canonical_codec_generated_available_v1()` returns `false`.

## Symptom
Before 2026-11-07 the spec never loaded: `use std.common.config.Logger` (Logger
lives at `compiler.common.config`), so 0 examples ran and the canonical arms
were never exercised. With the import fixed: 4/7 pass, 3 fail, all on the
canonical bounded path:
- line 78 "preserves a real function through canonical encoding and bounded decoding":
  `HirDecodeError::Unavailable(canonical_codec_generator_stale)`.
- line 86 "accepts the explicit wire fixture when both entry members are present":
  `hir_module_decode_bounded` returns the same Unavailable error.
- line 105 "rejects absent values and keys through the canonical bounded owner":
  the refusal is `Unavailable`, not `Malformed(missing_required_hir_module_function_entry)`.

## Cause
The canonical encode/bounded decode entry points stay closed by design until an
admitted self-hosted runtime regenerates `generated/hir_codec.spl` and an
independent lane freezes its real-HIR golden bytes (see
`hir_codec_generator_older_than_its_output_2026-10-23.md`).

## Unblock
Open `hir_canonical_codec_generated_available_v1` per that lane, then rerun the
spec; the three examples must pass unchanged. Do not weaken them.
