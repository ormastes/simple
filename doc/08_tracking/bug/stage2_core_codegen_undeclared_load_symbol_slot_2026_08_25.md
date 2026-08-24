# Stage 2 core_codegen references undeclared load_symbol_slot

## Status

Open. This blocks admission of the full Simple CLI and therefore blocks the
physical Vulkan Engine2D offload/readback acceptance run.

## Reproduction

Run the canonical full bootstrap in `dynload` mode at revision `bd80bccf77`,
stopping after Stage 2. The seed/runtime authority builds successfully, but the
Stage 2 native build fails one compile shard.

## Evidence

- Failing source:
  `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`
- Diagnostic:
  `llvm codegen: semantic: llvm global load referenced undeclared symbol load_symbol_slot`
- Failed shard count: 1
- Stage 2 was not admitted; Stage 3 did not start.
- Log:
  `build/bootstrap-gpu-dynload-final3/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`

This followed two distinct fixes which are already pushed: the Stage 3
post-HIR ExportAttr optional-payload segfault and same-module impl receiver
visibility routing. The final run stopped at the repository-mandated third
verify/fix cycle rather than retrying indefinitely.

## Required follow-up

Trace the `GlobalLoad(load_symbol_slot)` producer in MIR lowering and either
declare the symbol in the same LLVM module or correct the load to the intended
owner symbol. Add a focused `core_codegen.spl` native-build reproducer, rerun
the failed shard with its isolated cache, then perform a fresh admitted
bootstrap before running Vulkan device evidence.
