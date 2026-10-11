# Item 5 core-C Vulkan root native contract

Status: focused contract PASS; product size and demand-load qualification OPEN.

The isolated release-target branch at `808b798d375` contains the source
candidate that passes the selected runtime bundle to GNU native/shared link
support arguments. `test/fixtures/compiler/target5_core_c_vulkan_root_probe.spl`
was compiled with the admitted pure-Simple Stage 2 compiler, no codegen stub
fallback, entry closure, and `core-c-bootstrap`. Its two-module native build
completed and the executable exited 0 with
`TARGET5_CORE_C_VULKAN_ROOT_PASS`.

The fixture asserts that explicit core-C omits the forced Vulkan provider
symbol on Linux, macOS, FreeBSD, and MinGW spellings; host-GPU retains the
forced root; and no aggregate archive produces no support arguments. The
published probe SHA-256 is
`c71fdd9907a7b3813f5ef3e670cc8490aa12bc51885508d13274be58033075f4`
and its executable is 49,392 bytes. That byte count describes only this
two-module probe, not the Stage4 compiler or a before/after size comparison.

The live kernel closure audit still fails with two K0→OS imports in
`compiler.loader.module_loader_compat`: the DynSMF owned-query owner and the
SMF dynlib release owner. Moving those calls across SOSIX and qualifying
their runtime behavior remains part of Item 5. There is no current-source
full compiler link map, no matched C hello size/startup/RSS cohort, and no
Phase 7 demand-load PASS from this focused contract.

Evidence logs: `build/mini_builds/target5_core_c_vulkan_root_probe/build.log`
and `build/mini_builds/item5_kernel_closure_20261011.log` in the isolated
worktree.
