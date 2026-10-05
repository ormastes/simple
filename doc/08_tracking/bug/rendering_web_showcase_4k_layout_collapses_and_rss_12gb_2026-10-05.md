# rendering_web showcases at 3840x2160: layout collapses, `status=pass`, 12 GB RSS

- **Filed:** 2026-10-05
- **Area:** `examples/06_io/ui/rendering/rendering_web_{core,extended}.spl`
  (pass gate) × the seed JIT × `browser_engine` (memory)
- **Status:**
  - false pass: FIXED 2026-10-05
  - collapse: no longer reproduces on `origin/main` (see below)
  - memory: OPEN

## Symptom (2026-10-05, tree before #2524)

| entry | size | wall | max RSS | frame |
|---|---|---|---|---|
| rendering_web_core | 960x640 | 55 s | 2.76 GB | correct; byte-identical to the interpreter |
| rendering_web_core | 1920x1080 | 47 s | 6.51 GB | correct |
| rendering_web_core | 3840x2160 | 39 s | 5.82 GB | **near-blank**: one 190x94 box |
| rendering_web_extended | 3840x2160 | 40 s | **12.36 GB** | **collapsed**: section cards shrank to 392-px columns |

Both 4K runs printed `showcase status=pass`. The only gates were
`pixels.len() == w*h` and `checksum != 0`.

## False pass: fixed

`rendering_web_frame_verdict` (`examples/ui/rendering_web_core`) now gates
both examples. The page body is `main { width: min(1100px, 100%) }`, so a
laid-out frame must satisfy two conditions:

- content spans at least 80% of `min(w, 1100)` across and at least 50% of
  `min(h, 1000)` down;
- a white section card is at least 75% of that width wide.

Otherwise the example prints `showcase status=fail reason=collapsed-layout ...`
and exits 1. Applied to the saved captures:

| capture | verdict |
|---|---|
| old near-blank core | `collapsed-layout content=190x94 want>=880x500` |
| old collapsed extended | `collapsed-layout card-width=392 want>=660` |
| current 4K core | pass |
| current 4K extended | pass |
| current 960x640 core | pass |

The spec `test/01_unit/app/ui_showcase/rendering_web_frame_verdict_spec.spl`
(5/5) covers blank, near-blank, narrow cards under a full-width header, a good
page, and a size mismatch.

## Collapse: gone on current main

On `origin/main` at 84c231b6b77, both pages lay out correctly at 3840x2160,
in the same geometry as 1920x1080:

- core: content x=7..1092, y=24..1190;
- extended: correct cards and tabs.

The broken captures were taken before #2524. That PR fixed inlined float
parameters reaching float→int casts as raw f64 bits
(`jit_inlined_float_param_cast_reads_f64_bits_as_int_2026-10-05.md`), which
corrupted layout math. That fix is the likely cause of the recovery, but this
is not proven by a bisect.

Separate layout defect seen in the probes (`browser_engine` / CSS lane):
`main { margin: auto }` does not centre the 1100-px column. It stays at x=0 at
every viewport width from 1920 to 3840.

## Memory: open

`rendering_web_core`, JIT, this tree:

| size | max RSS |
|---|---|
| 320x240 | 4.25 GB |
| 3840x2160, with capture | 6.90 GB |
| 3840x2160, no capture | 6.66 GB |
| 3840x2160, extended | 8.39 GB |

Most of the memory is a size-independent ~4.2 GB baseline: compiling and
splicing the `browser_engine` closure, measured at 320x240. The 4K frame adds
about 2.4 GB, roughly 70 copies of a 33 MB ARGB frame. The PPM capture adds
only about 0.25 GB.

Next steps:
- attribute the baseline (JIT compile versus hybrid interpreter splice);
- find which pipeline stage holds frame-sized `[u32]` copies.
