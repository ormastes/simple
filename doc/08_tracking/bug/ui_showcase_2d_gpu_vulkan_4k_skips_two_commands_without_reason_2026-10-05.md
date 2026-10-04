# 2D GPU showcase on Vulkan at 3840x2160 skips two commands with no fallback reason

- **Filed:** 2026-10-05
- **Area:** `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` (composition executor)
  × `src/app/ui_showcase/hosts/host_2d_gpu.spl` (receipt check)
- **Status:** OPEN (pre-existing; it also reproduces in the interpreter)

## Repro

```
SIMPLE_GPU_BACKEND=vulkan SIMPLE_SHOWCASE_W=3840 SIMPLE_SHOWCASE_H=2160 \
SIMPLE_SHOWCASE_FRAMES=1 <seed> run src/app/ui_showcase/hosts/main_2d_gpu.spl
showcase status=fail renderer=vulkan reason=metal-drawir-receipt-rejected
```

The result fields, from a temporary print in `_accept_result`:

```
sel=gpu fb=false fr= skip=2 rend=59 rb=device_readback h=31 dev=1
ck=293706980 px=8294400 exp=8294400
```

Everything is valid except `skipped_command_count=2`, and those skips carry
**no** `fallback_reason`. The same scene at 320x240 renders all commands and
passes (JIT and interpreter captures are byte-identical). The interpreted 4K
run failed with this same reason on 2026-10-04 (644 s, 4.3 GB), so this is not
a JIT regression.

## Leads

In `draw_ir_adv.spl`, the paths that count a skip without naming a kind are
the text branch (`drawn = false` from `draw_text_with_advances_vulkan_only`,
~line 2978) and `submit_batch()` returning false (~line 2991). A 4K-only
failure points at a size-dependent budget, for example the font glyph cap or
the glass/blur work budget. The fix should make the skip name its reason
(fail-closed) before deciding whether the budget itself is wrong.

## Measured after the 2026-10-05 JIT fixes

The 4K JIT run finishes in 129 s with 2.6 GB max RSS (previously >900 s in the
interpreter). Only this receipt check remains.
