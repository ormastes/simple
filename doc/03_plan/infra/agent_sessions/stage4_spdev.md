# Lane: stage4 / $sp_dev remake plan (ex-codex 019f9c04)
Goal: "$sp_dev remake plan; do all item tasks in parallel."
Last state: parser ambiguity in `src/compiler/70.backend/backend/vulkan_backend.spl` was patched by replacing `if ... else` expression-form branches with explicit `if ... return` blocks.
Current status: stage4 native-build now reaches parse completion; no parser errors from `vulkan_backend.spl`.
Blocking: stage4 consistently crashes with segmentation fault during phase3 hir lowering (`[hir-lower] lower_expr:kind`) after `phase3:hir_typecheck` begins, exit code 139.

Parallel execution split is now defined in
[`doc/03_plan/agent_tasks/stage4_spdev.md`](doc/03_plan/agent_tasks/stage4_spdev.md)
with Team A–D lanes and merge/final-review ownership.

Recent commands:
- Ran direct stage4 native-build command with `SIMPLE_NATIVE_BUILD_THREADS=4`; logs: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build-current.log`; result `EXIT:139`.
- Ran same command with `SIMPLE_NATIVE_BUILD_THREADS=1` (to exclude concurrency effects); logs: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build-threads1.log`; result `EXIT:139`.

Next: classify phase3 `hir_lower` segfault and either bisect or escalate with compiler/runtime team; do not re-run full native-build until blocker is isolated/fixed.
