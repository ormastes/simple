# Native codegen leaves escapes unprocessed after a `{` in a text literal

**Status:** OPEN. **Found:** 2026-11-26 (work/bug-cuda-module-get-function-abi-20261126). **Severity:** P2.
**Component:** native (LLVM) lowering of string literals. Observed on the integ25 Stage 2 compiler
(`pinned-c1a10190b978`, stage2-admitted sha256 `ef46f0d2ab4274c4`); not re-checked on current source.

A literal like `"a\n) {\n    b;\n}\n"` evaluates to 573 bytes for the
probe PTX under the interpreter (W-STR-BRACE-001 warns and keeps `{` as
text). The NATIVE binary built from the same source passes 591 bytes: every
`\n` after the `{` reaches the runtime as the two bytes `\` `n`. Writing
`{{` gives the same 591 bytes. Seen with gdb at the
`rt_cuda_module_load_data` call (`x1 = 0x24f`, text `... count\n) {\\n    .reg ...`).

Effect: PTX embedded in Simple source is rejected by the driver with -218
`CUDA_ERROR_INVALID_PTX` in native builds. `src/lib/gc_async_mut/processing/cuda_fill_u32.spl:41`
(`_processing_cuda_ptx`) has the same shape, so the native ProcessingIR CUDA
path is likely affected.

Workaround (used in `src/app/test/cuda_module_launch_probe.spl`): put each
brace in its own literal, `... ") " + "{{" + "\n..."`. Then interpreter and
native both give 573 bytes, and the module loads.
