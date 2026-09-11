# vk2d_bench hardcoded block reason — FIXED 2026-09-11

`test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl` printed
`status=blocked reason=unconditional-submit-wait` from a hardcoded string
literal at the end of `Vk2dBench.run()` (formerly line 173), regardless of
what the Vulkan backend actually reported. `completion_count` (fence
completions, tracked correctly per frame via
`self.engine.vulkan_submission_generation()`) was computed and printed as
`fence_completions=`, but never consulted to decide `status=`/`reason=` — the
bench could never honestly report `status=pass`.

## Fix

Added `Vk2dVerdict` and `vk2d_verdict(backend, frames, fence_completions)`
(`test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl:19-34`), computing the verdict
from real evidence:

- `backend != "vulkan"` -> `status=blocked reason=backend-unavailable`
- `frames <= 0` -> `status=blocked reason=zero-frames`
- `fence_completions == frames` -> `status=pass`, `submits_per_frame=1`
- otherwise -> `status=blocked reason=multi-submit-per-frame:<n>`,
  `submits_per_frame=fence_completions/frames`

`Vk2dBench.run()` now calls `vk2d_verdict(self.engine.backend_name(), frames,
completion_count)` (`vk2d_bench.spl:185-190`) and emits the computed
`status=`/`reason=` plus a new `submits_per_frame=` key; every other
`key=value` in the output line is unchanged.

## Spec

`test/05_perf/bench/vulkan_2d_c/vk2d_bench_verdict_spec.spl` — 4 absolute
oracles against `vk2d_verdict` directly (imported via `use .vk2d_bench.{vk2d_verdict}`,
a relative import; `bench.vulkan_2d_c.vk2d_bench` does not resolve as a module
path from `test/`):

- `("vulkan", 300, 300)` -> `status=pass`, `submits_per_frame=1`
- `("vulkan", 300, 600)` -> `status=blocked reason=multi-submit-per-frame:2`
- `("cpu", 300, 300)` -> `status=blocked reason=backend-unavailable`
- `("vulkan", 0, 0)` -> `status=blocked reason=zero-frames`

Run: `bin/simple run test/05_perf/bench/vulkan_2d_c/vk2d_bench_verdict_spec.spl`.

**Sabotage/fix triple** (restored the original hardcoded literal, reran, restored the fix):

1. Fixed code: `4 examples, 0 failures` (`outcome=OK executed=4 passed=4 failed=0`).
2. Sabotage (literal `Vk2dVerdict(status: "blocked", reason: "unconditional-submit-wait", submits_per_frame: 0)`
   restored in place of the real logic): `4 examples, 4 failures`
   (`outcome=ERROR executed=4 passed=0 failed=4`) — every example failed with
   an exact mismatch (e.g. `expected 0 to equal 1`, `expected
   unconditional-submit-wait to equal backend-unavailable`).
3. Fix restored: `4 examples, 0 failures` again.

## Real-device run (macOS, aarch64-apple-darwin-macho)

Binary: `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`
— `stat -f 'size=%z mtime=%m'` before and after: `size=26264696 mtime=1788766698`
(unchanged, confirms the binary that ran is the one that was inspected).

Command:
```
SIMPLE_LIB=src VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json \
VK2D_W=900 VK2D_H=760 VK2D_FRAMES=300 \
/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple run \
  test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl
```

Output:
```
simple-vulkan-2d status=blocked reason=backend-unavailable requested=vulkan got=cpu
```

This host's deployed Vulkan (MoltenVK) backend is unavailable to
`Engine2D.create_with_backend_fast` in this environment (falls back to
`cpu`), so `main()`'s existing pre-flight check
(`vk2d_bench.spl` around the `engine.backend_name() != backend` guard) returns
before `Vk2dBench.run()` is ever called. This is an honest, non-fabricated
`status=blocked reason=backend-unavailable` line — consistent with, and
produced by the same reason taxonomy as, the new `vk2d_verdict` logic (the
pre-flight check in `main()` predates this fix and already used this reason
name; `vk2d_verdict` reuses it for the case where the backend is discovered
mid-`run()`). No pass/blocked-multi-submit evidence could be captured on this
host because the Vulkan backend itself is unavailable here — that is a
separate, pre-existing environment gap, not a defect in this fix.
