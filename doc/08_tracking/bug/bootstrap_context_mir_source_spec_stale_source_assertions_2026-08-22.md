# `bootstrap_context_mir_source_spec` is a stale source-text spec, not a link failure (2026-08-22)

**Status:** OPEN (test-side; 12 of 16 examples fail on trees >= 1c8757fb745 with every seed).

The run8 deploy gate flagged `test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl`
(16 examples, 12 failures) and the failure text starts with
`error: LLVM native linking failed: Linking failed: cc linking failed:`, which
reads like a toolchain problem. It is not:

- The spec never links anything. It `rt_file_read_text`s
  `driver_bootstrap.spl`, `driver_aot_native_output.spl`, `driver_types.spl`,
  `driver_aot_pipeline.spl`, ... and asserts that those SOURCES contain fixed
  snippets; the "cc linking failed" string is inside the *expected* text block
  (`driver_native_link_undefined_symbols` rendering) that the spec was written
  against.
- Controls: deployed seed `dee19c5` 16/12; candidate `1c8757fb745` 16/12;
  candidate with `. scripts/setup/llvm-toolchain-env.shs` sourced
  (`CC=clang-23 LD=ld.lld-23`, LLD 23 first on PATH) **still 16/12** — the
  toolchain is irrelevant.
- Failing examples: "uses requested native-build entry module for bootstrap
  MIR lowering", "lets Stage4 reach the full pure Simple native output path",
  "uses source fingerprints instead of raw module cache hits for native
  dynload", "keeps bootstrap HIR lowering keyed and named by the requested
  module", ... — i.e. the driver sources were refactored today (object-cache
  entry fix 809ce6d4e71, HIR registry memo, CodegenTarget fix) and the frozen
  snippets no longer match.

Action: re-baseline the snippets against the current driver sources, or
replace the text assertions with behavioural ones (the object-cache
second-build spec already covers the cache half). Not a deploy blocker;
`scratchpad/fp8/gate.sh` treats it as tree-side.
