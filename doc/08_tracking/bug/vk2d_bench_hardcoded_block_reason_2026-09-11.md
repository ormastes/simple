# vk2d_bench hardcoded block reason — FIXED 2026-09-11

**Status:** OPEN (unverified 2026-09-12)

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
— `stat -f 'size=%z mtime=%m'` unchanged across every run below:
`size=26264696 mtime=1788766698`.

**First attempt (misleading — corrected below).** Without
`SIMPLE_EXECUTION_MODE=interpreter`, the default JIT-lane invocation reported
`status=blocked reason=backend-unavailable requested=vulkan got=cpu` — MoltenVK
initialization did not survive the JIT execution path on this host, causing
`Engine2D.create_with_backend_fast` to fall back to `cpu` before
`Vk2dBench.run()` was ever reached. This is not a defect in `vk2d_verdict` (it
never ran), but it was the wrong invocation for this host: two other agents
had already reached `device=Apple M4` today with the same binary via the
interpreter execution mode.

**Corrected run**, exactly matching the working invocation used elsewhere
today:
```
SIMPLE_LIB=src VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json \
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 \
VK2D_W=900 VK2D_H=760 \
/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple run \
  test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl
```

Full output line:
```
scene_source=table rects=64
simple-vulkan-2d status=pass w=900 h=760 rects=64 warmups=5 samples=300 ring=1 max_frames_in_flight=1 unconditional_submit_wait=true submits_per_frame=1 timed_buffer_allocation_count=-1 retained_buffer_bytes=-1 teardown_released_bytes=-1 timed_full_frame_upload_count=-1 upload_bytes=-1 timed_readback_bytes=0 capture_count=0 capture_readback_bytes=0 capture_source=none fence_completions=300 completion_polls=0 cpu_completion_wait_count=300 event_generations=300 damage_area_pixels=205200000 p50_ns=39830000 p95_ns=50213000 ms=12589 fps~=23 draw_us=11949759 finalize_us=620568 device=Apple M4 driver=Apple M4|vendor=0000106b|device=1a040209|driver=000028a1|api=0040014e checksum=0
```

Verdict fields: `status=pass reason=<empty> submits_per_frame=1 ms=12589`
(`fence_completions=300 == samples=300`, so `vk2d_verdict("vulkan", 300, 300)`
computes `status=pass`, matching the spec's first oracle exactly). `device=Apple
M4` confirms the real Vulkan/MoltenVK backend ran, not `cpu`.

No code change was needed to reach this result — `vk2d_verdict` and the
pre-flight `engine.backend_name() != backend` guard in `main()` are unchanged
from the earlier commit; the only difference was
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0` in the invocation,
which this repo's JIT/interpreter split apparently requires for this backend
on this host. Root-caused the JIT-vs-interpreter Vulkan-init discrepancy only
to this env-var workaround; the underlying "MoltenVK does not survive the JIT
execution path" gap is separate from this bench's status-literal defect and is
not further investigated here.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
