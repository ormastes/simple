# Product source overlay omitted the counterpart SDK header

The Windows scalar diagnostic from producer `27ac2358f22f28c9a43ec3ab47ac3957d5e2b293fc8b44fc52e573512f0c4c69` completed HIR/MIR but failed runtime compilation because `src/runtime/counterpart_abi_runtime.c` includes `../../tools/counterpart/sdk/c/simple_counterpart_abi.h`. The product overlay selected `src/runtime` without selecting that required SDK directory.

The shared construction/verification membership policy now includes `tools/counterpart/sdk/c`. The real filesystem regression checks exact header bytes, relative include resolution, and rejection of header mutation. This repairs an input-closure defect; it does not establish a numeric payload fix, successful native product compilation, or release admission.

Evidence: `windows-restart-20261004/scalar-probe-owner-retry1/cranelift/numeric_payload_boundary_trace/compile.log`. Preserve that failed generation. A successor must use a fresh overlay and its own authenticated source inventory.
