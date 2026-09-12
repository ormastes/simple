# The css-layout catalog page renders NON-DETERMINISTICALLY at 900x760 on the Vulkan lane (macOS M4, 2026-09-12)

Status: **OPEN, pre-existing, not caused by any change in this lane.** Filed
because it silently invalidates frame-checksum and PPM comparison as a
before/after oracle at this size — and has already caused one correct patch to
be backed out.

Binary bracketed identical on every run: `/Users/ormastes/simple/build/cargo-r2/release/simple`,
`stat -f '%z %m'` = `39368072 1789171430`. Page
`examples/06_io/ui/web_catalog/css-layout.html` at 900x760,
`SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native SIMPLE_2D_BACKEND_STRICT=1
SIMPLE_EXECUTION_MODE=interpreter`, one run at a time. Logs:
`build/perf/vk_attr_2026-09-12/` (gitignored).

## The observation

Seven runs across four source variants produced **three distinct whole-frame
checksums**, and the variants do not partition them:

| run | product logic | checksum |
|---|---|---|
| `vk900_before` | no host mirror | 2936851417192293 |
| `vk900_after` | mirror, invalidate inside dirty branch | 2936851411469080 |
| `vk900_after_rep` | *identical tree to the row above* | 2936851411469080 |
| `vk900_fix2` | + invalidate at function entry | 2936851404759230 |
| `vk900_fix3` | + require generation continuity (strictly stricter) | 2936851411469080 |
| `vk900_diag` | fix3 + a READ-ONLY self-check | **2936851417192293** |

Two facts kill every "the change moved the pixels" reading:

1. **A strictly stricter variant (`fix3`) returned a looser variant's value**,
   and `pack_full=8 pack_incremental=13` was identical across all of them — the
   guard conditions never changed which batches took which path.
2. **`vk900_diag`, which runs the mirror ACTIVELY (13 incremental repacks),
   produced exactly the no-mirror baseline checksum.** A change cannot both
   alter pixels and reproduce the unaltered pixels.

## The incremental repack is independently PROVEN correct

`SIMPLE_VK_FONT_SELFCHECK=1` compares the host mirror against a full pack of the
same atlas after every incremental repack — the ground truth, computed by the
same function the full path uses. Result on the 900x760 page:

```
font_mirror_selfcheck checks=13 bad_calls=0 bad_bytes=0 first=[]
```

**13 incremental repacks, zero mismatching bytes.** The per-composite decision
log also shows the guard behaving exactly as designed: every incremental repack
has `host_gen == gen - 1` with `owner_match=true`, and every full repack is
caused by `owner_match=false`, i.e. a genuine font-face change.

So the mirror is byte-exact, and the frame checksum still moves. The divergence
is downstream of the font atlas entirely.

## Why this matters beyond this lane

`doc/08_tracking/bug/web_catalog_vulkan_lane_raster_term_2026-09-12.md` records
that F14's corner-sprite coalescing was measured at **-13.7%** and then **held
back** because "at 900x760 the frame checksum MOVED (2936851399036017 ->
2936851411469080)". That value, `2936851411469080`, is one of the three this
page produces on its own with no coalescing anywhere in the tree. **A correct
optimisation was very likely backed out on noise.** Anyone re-measuring that
patch must use a different oracle.

## What to use as an oracle instead, until this is fixed

- 300x253 IS stable: every run in this lane produced `325932497106919` and
  byte-identical PPMs. Use it for pixel equality.
- At 900x760, compare against an INVARIANT the change is supposed to preserve
  (the mirror self-check above), not against a whole-frame checksum.

## Where to look

Nondeterminism appears at 900x760 and not at 300x253, and the two differ in
exactly the offscreen-group path: 900x760 reports `image=2 readbacks=3`, while
300x253 reports `image=0 readbacks=1`. That is also where the 900x760 time goes
— `_draw_image_composite_native` is 544 s of a 789 s frame with a single call
reaching 179 s (see
`doc/10_metrics/ui/web_catalog_vulkan_per_op_attribution_macos_2026-09-12.md`).
A composite whose cost varies by two orders of magnitude between calls and a
frame whose pixels vary between runs are plausibly the same defect: a
flush/fence or descriptor-pool reuse whose ordering is not pinned. Not
confirmed — no probe in this lane measured it.
