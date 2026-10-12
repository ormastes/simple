# Conversion import ownership: current-owner regression evidence

Status: nine runtime assertions passed; intended frozen-source admission remains HOLD. No native compiler or product qualification.

The frozen grouped Phase1 run warned that `bytes_to_text` was absent from `std.common.base_encoding.utilities` and `text_to_bytes` was absent from `std.common.cbor.types`. Four malformed UTF8 expectations and one newline rejection failed. The declared functions are `base_encoding_bytes_to_text` and `cbor_text_to_bytes`. This is the same missing-export group recorded in [the earlier report](utf8_guard_specs_import_removed_conversion_names_2026-10-11.md); this report adds a distinct retained execution and its limits, without modifying that report or the dirty original specs.

The new [regression spec](../../../test/01_unit/lib/common/conversion_import_binding_spec.spl) imports those declared names explicitly, including aliases. Five cases preserve the observed failures; four controls distinguish canonical and aliased calls from the raw replacement decoder and unrestricted encoder. All assertions invoke actual library functions. No conversion implementation changed, and no stub, constant-only assertion or original passing case was substituted.

## Retained execution

One bounded Phase1 diagnostic used bootstrap seed SHA256 `d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`, the canonical `test_runner_single.spl`, requested interpreter mode, a 120-second Job bound and 30-second row bound. Actual interpreter versus JIT dispatch ownership was not independently verified. It exited 0, final Job active count 0, peak RSS 214684 KiB. The trusted reader reported 9 executed, 9 passed, 0 failed, 0 deferred and no truncation. ANSI-stripped output matches all nine unique case names; target import warnings are absent. The passing criteria were not rerun.

Packet: `build/native_probe/utf8-cbor-import-route-20261013-astra/candidate-cycle2/`.

- Tested fixture SHA256: `0e8d80ebc353e3e84bd36178eb543e43c939c9bf4a278f7f2a09b37a2485faf7`.
- Landing spec SHA256: `f1cedeb52adc12fd98d440caeb3a188bcb7afb725b69fecb182022b9b48cd024`. Only the stale private/unrun header changed; the executable body is byte-identical.
- Receipt SHA256: `95e4ba7367837816edf9bbc189c4d21ed1b19d7b06f649fbb2ffd0c6adfc886d`.
- Log SHA256: `6356791a9a23350a640d657199cdee6c807fa03667a33bea565261da394331b0`.
- Retained supplement SHA256: `068a9b495f95833988c3ef20f62ef2ecf243576f63c3bd8596da6cee1f53f949`.

## Admission limit and resolver prerequisite

The private fixture physically under `C:/dev/simple/build` resolved imports into the shared repository, despite frozen cwd and `SIMPLE_LIB`. Eleven outside reads invalidate frozen-closure admission. Actual binding traces select the shared canonical utility and CBOR functions. All three conversion owners match their recorded pre-execution hashes; the utility target body matches the frozen body, although its whole module differs. Other shared dependency preimages were not authenticated, and the original fixture consumed-byte trace remains absent. Original `RESULT.json` stays HOLD; the supplement records narrower current-owner runtime observations.

Current and frozen Rust `interpreter_module/path_resolution.rs` search an importer ancestor containing `src` or `Cargo.toml` before the cwd project. This is consistent with observed paths, but does not prove the seed's exact build-source mapping. A separate tiny resolver-boundary diagnostic is proposed and unrun. No nine-case replay, new seed build, pure runtime parity or native qualification is implied.
