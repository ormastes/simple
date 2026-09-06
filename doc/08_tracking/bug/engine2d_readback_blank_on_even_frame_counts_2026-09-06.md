# engine2d readback returns a blank frame on EVEN present counts, and present costs a fixed 18.4 ms/frame

**Filed:** 2026-09-06
**Severity:** high — the readback defect is silent and deterministic; any
evidence gate that renders an even number of frames and checksums the result is
checksumming a blank image and calling it a pass.
**Area:** `engine2d` 2D lane (`Engine2D.present` / `read_pixels_with_source`)
**Found by:** driving `test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl` at small
sizes under `SIMPLE_EXECUTION_MODE=interpret` (the JIT lane aborts on aarch64 —
see `jit_aarch64_branch_relocation_out_of_range_abort_2026-09-05.md`).

## Defect 1 — readback is blank on even present counts

`checksum` is correct for odd frame counts and exactly `0` for even ones.
9 of 9 runs agree, and repeats are deterministic (frames=8 twice, both `0`):

| frames | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 10 |
|---|---|---|---|---|---|---|---|---|---|
| checksum | -15461356 | **0** | -15461356 | **0** | -15461356 | **0** | -15461356 | **0** | **0** |

The bench also issues 2 warm-up presents before the timed loop, so the parity
that matters is of the TOTAL present count, and `0` means the readback sampled a
surface that was never drawn into. That is the signature of a two-buffer
ping-pong where `read_pixels_with_source` reads the buffer that was *not* just
presented.

Why this is worse than a wrong number: `0` is also what a correct readback of a
fully transparent surface would produce, so a gate that only asserts
"checksum is stable" or "no mismatch" cannot tell the two apart.

Reproduce (any even value blanks it):

```
SIMPLE_EXECUTION_MODE=interpret SIMPLE_LIB=src \
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json \
VK2D_W=64 VK2D_H=64 VK2D_RECTS=1 VK2D_FRAMES=4 \
  <vulkan-feature seed> run test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl
```

## Defect 2 — `present` is a fixed ~18.4 ms per frame

`present_us` is strictly linear in frame count and independent of both
resolution and rect count:

| frames | present_us | per frame | total ms |
|---|---|---|---|
| 1 | 18463 | 18463 | 24 |
| 3 | 55487 | 18496 | 73 |
| 8 | 146631 | 18329 | 192 |

That is **~76% of frame time spent in present**, and it pins the lane at a
constant `fps~=41` across every workload measured — the reported fps did not
move between 1 and 8 frames, or between a 64x64 single rect and larger scenes.
A per-frame cost that ignores how much was drawn is not rendering work; 18.4 ms
is also suspiciously close to a 60 Hz vblank (16.7 ms), which an offscreen
headless render has no reason to wait for.

Not yet isolated to a specific wait — recorded with the measurements so the
next reader starts from data rather than from scratch.

## Related, and probably load-bearing

`rt_vk_present`, `rt_vk_readback` and `rt_vk_submit` are **unbacked externs** —
declared in `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl`
and `src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl`, defined in no
`.rs`/`.c`/`.h`, and absent from the built binary (`nm` and `strings` both find
nothing). All three are already carried in
`scripts/check/unbacked_extern_baseline.txt` as known debt, so this is not new
breakage — but per
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md` an unbacked
extern returns nil silently, which means the `backend_vulkan_session` Simple API
cannot be doing what its name says. Whatever produced the pixels above was not
that path. Establishing which backend actually serviced these runs is the
natural next step and is NOT settled here: a `VK2D_BACKEND=vulkan` vs `=cpu`
comparison produced no result line for either within the timeout, so no
conclusion is drawn from it.
