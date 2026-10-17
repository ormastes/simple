# Required function codec generator freshness

Authored manual for `test/01_unit/app/compiler_schema/hir_required_function_codec_generation_spec.spl`. Status: TEST_BLOCKED; one scenario authored, not executed.

From the repository root, load the actual HIR declaration universe with `CodecUniverse.load` and render through production `emit_codec_file`. Require nonempty output, the required-entry writer and reader refusal branches, and guarded function-dictionary insertion. Finally compare the complete generated output with `src/compiler/20.hir/generated/hir_codec.spl`.

This exercises the authoritative generator rather than a copied emission algorithm. It does not compile or run the generated decoder. Runtime malformed-input/body-roundtrip coverage is authored separately in `hir_codec_required_functions_spec.spl`. Exact generation, executable tests and normal bootstrap admission remain pending.
