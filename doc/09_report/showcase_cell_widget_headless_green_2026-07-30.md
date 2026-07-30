# Showcase matrix — cell "widget x headless (interpreted)" verified GREEN on linux-x86_64

Date: 2026-07-30T18:11:12Z
Host: x86_64-linux

## Verdict

**GREEN.** Every value pinned by the CLAIMED result reproduces **exactly**
on this host with today's canonical binary — primary (640x480) and
secondary (320x240) alike.

Pass criteria were fixed **before** the first run (the cell's claim is more
diffuse than cell 2's single checksum, so the bar was written down first to
stop it drifting to fit the result):

| # | Criterion (declared up front) | Claimed | Observed | |
|---|---|---|---|---|
| 1 | 640x480 P6 PPM artifact | `P6 640 480 255` | `P6 640 480 255` | match |
| 2 | nonzero pixels | 921,600 / 921,600 | 921,600 / 921,600 | match |
| 3 | distinct byte values | 74 | 74 | match |
| 4 | widget types | 24 | 24 | match |
| 5 | font raster cold / warm-hits | 10 / 20 | 10 / 20 | match |
| S | 320x240 repeat, distinct bytes | 64 | 64 | match |

Supporting trace: `showcase_font_loaded=true`,
`showcase_font_backend_attempt_succeeded=true`,
`showcase_font_identity=sha256=c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f;axes=static`
(identity equals `showcase_font_expected_identity`),
`showcase_renderer_backend=software`, `showcase_frame_dimensions=640x480`,
`showcase_font_execution_target=cpu`
(cuda/metal/opencl/vulkan/rocm unavailable, cpu success).

Note on units: the claim's "921,600 nonzero px" counts **RGB bytes**; the
program reports `rendered 307200 px`, and 307,200 px x 3 = 921,600 bytes,
which is exactly the PPM payload. Consistent, not a discrepancy.

## Provenance

- source commit: `a7a5bb3c0f28781f0f4233d41b6b9ef806365366`
- binary: `bin/release/x86_64-unknown-linux-gnu/simple`, sha256
  `ea4af9a4498297e3c4f31ca7…`, 154,095,344 bytes — the canonical
  `--profile bootstrap --features llvm` build (4/4 provenance markers,
  `llvm::`=617, `lld::`=0), copied to `build/tmp/claude_simple` for the run
- entry: `examples/06_io/ui/widget_showcase_gui.spl` (the true `examples/`
  path, resolved from `WIDGET_SHOWCASE_APP_SOURCE` in
  `src/lib/common/ui/wm_app_process_contract.spl:48`)
- lane: interpreted, software offscreen, headless
- `find assets/fonts -type f | wc -l` = **57** (verified before the run)

## Artifacts

| Run | File | Size | Payload sha256 | checksum | elapsed |
|---|---|---|---|---|---|
| 640x480 | `widget640.ppm` | 921,615 B (15 B header + 921,600) | `9c6b02ff035fcaa23c6956a4…` | `1863705433` | 95 s |
| 320x240 | `widget320.ppm` | 230,415 B | — | `1402715751` | 46 s |

Whole-file sha256 of the 640x480 PPM:
`aa3096a646684582952c5c0b4b37d4a9069540db7d3c2cd2151032c93e9fdc78`.

## Reproduce

```sh
# In a worktree checked out at the target commit — NOT the shared working
# copy, whose HEAD predates the font restore cdadda01da2 and which also has
# core.sparseCheckout=true, so assets/fonts is empty with a clean git status.
find assets/fonts -type f | wc -l      # must print 57 before starting

mkdir -p build/tmp
cp bin/release/x86_64-unknown-linux-gnu/simple build/tmp/claude_simple
SIMPLE_SHOWCASE_TRACE=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
SIMPLE_TIMEOUT_SECONDS=0 SHOWCASE_RESOLUTION=640x480 \
SHOWCASE_PPM=/tmp/widget640.ppm \
  build/tmp/claude_simple run examples/06_io/ui/widget_showcase_gui.spl
```

Both env knobs are mandatory: the protected binary name keeps
`kill_simple_monitor.shs` from SIGTERM-ing a ~95 s render at 60 s, and
`SIMPLE_TIMEOUT_SECONDS=0` disables the hard 10 s timeout `bin/simple run`
applies to any path containing `examples/`.

`SHOWCASE_PPM` is required to obtain the artifact at all: without it the
run ends `No GUI requested … headless only.` and writes no file, so
criteria 2 and 3 cannot be evaluated. Criteria 1/4/5 are visible in the
trace either way.

## Demotion guard (not triggered)

Per the cell-2 lesson, a checksum mismatch alone is not a demotion: if
`nonzero` and widget-type counts still match while glyph-sensitive values
drift, that is the signature of "the render ran but a resource was
missing" (typically the absent font tree), not of a broken cell. This run
needed no such judgement — every declared value matched on the first
properly-configured attempt.
