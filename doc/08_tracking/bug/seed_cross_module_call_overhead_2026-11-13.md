# Seed interpreter: an imported function call costs measurably more than a module-local one

- Date: 2026-11-13. Lane `work/spy-xray-2-20261113`.
- Binary: Rust seed `src/compiler_rust/target/bootstrap/simple` (sha256 `df9dfb057afb7b8f…`,
  2026-11-05 18:12), interpreter lane (the probe's JIT attempt falls back on
  `Cannot infer field type: CoffObject.sections`).

## Observation

`linker/coff/coff_object.spl` parsing a 626,353-byte clang `x86_64-pc-windows-msvc` object
12 times (`coff_parse_object`), 4G scope, alternating runs:

| `_coff_u16/_coff_u32/_coff_i16/_coff_i32/_coff_fixed_name` | wall s |
| --- | --- |
| module-local bodies (old) | 15.89 / 15.90 / 15.47 / 15.40 / 15.90 |
| the byte-identical bodies in `std.common.pe.pe_image_v1`, imported with `use ... as _coff_u16` | 17.26 / 17.24 / 17.11 |
| local bodies again, header/section-header structs shared | 15.72 / 16.28 |

Same bodies, same call count; only the defining module differs. ~8% of a whole parse.

## Impact

Sharing small hot helpers across modules (the MDSOC direction) is penalised on the
interpreter lane; the linker keeps local copies of these five readers until this is fixed.

## Next step

Profile the interpreter's cross-module call dispatch (symbol resolution per call vs a cached
callee). Re-measure with the probe recipe in
`doc/03_plan/compiler/aspect_dynload/xray_v1_integration_status_2026-11-03.md` "Step 3e" and
fold the readers when the gap is gone.
