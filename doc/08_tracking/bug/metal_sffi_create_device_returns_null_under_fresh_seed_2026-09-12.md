# `metal_sffi_create_device(0)` returns 0 under the fresh seed — cargo `metal` feature was OFF

**Status:** ROOT-CAUSED. Not a runtime defect, not a registration gap — a build
feature-gate defect in an ad-hoc seed, plus the absence of any repo artifact that
codifies the seed's GPU feature list.

**Date:** 2026-09-12 · **Host:** Apple M4, macOS (Darwin 25.5.0)
**Seed under test:** `build/cargo-r2/release/simple`, 39,368,072 B, mtime 1789171430
(built `--features vulkan,vulkan-graphics`)

## Symptom

`test/02_integration/rendering/metal_msl_pipeline_spec.spl` is 7 examples /
5 failures on a real Apple M4, and the direct probe answers zero:

```
use std.io.metal_sffi.{metal_sffi_create_device}
fn main():
    print "device={metal_sffi_create_device(0)}"
```
→ `device=0`

Filed downstream of `doc/08_tracking/bug/lane4_metal_and_vulkan_backend_specs_red_2026-09-12.md`,
which observed the symptom correctly but mis-attributed it (see "Correction").

## Root cause

`rt_metal_create_device` is compiled to its stub. Every `rt_metal_*` entry point
in `src/compiler_rust/runtime/src/metal_graphics_runtime.rs` is written as a
pair:

```rust
#[no_mangle]
pub extern "C" fn rt_metal_create_device(_device: i64) -> i64 {
    #[cfg(all(target_os = "macos", feature = "metal"))]
    { metal_impl::create_device(_device) }
    #[cfg(not(all(target_os = "macos", feature = "metal")))]
    { 0 }
}
```
(`metal_graphics_runtime.rs:976-986`; the same shape repeats for ~30 `rt_metal_*`
functions.)

The seed was built `--features vulkan,vulkan-graphics`. The cargo feature
`metal` — `simple-driver/metal` → `simple-compiler/metal` → `simple-runtime/metal`
→ `dep:objc2-metal` etc. (`driver/Cargo.toml:105`, `compiler/Cargo.toml:53`,
`runtime/Cargo.toml:30`) — was never named, so the `cfg(not(...))` arm won and
**every Metal call returns 0 while the symbol is still present and exported**.
That is why `rt_metal_create_device` appears 7 times in the binary's string
table: the stub is real code with a real symbol, it just always answers zero.

`MTLCreateSystemDefaultDevice` was never reached. There is no dlopen gate, no
`SIMPLE_METAL_*` env gate, and no headless restriction involved.

## Correction to the lane 4 record

The lane 4 record called this "a registration / feature-gate gap ... the
`unregistered extern silently returns nil` class". The **feature-gate** half is
right; the **registration** half is wrong and should not be carried forward:

- `rt_metal_create_device` **is** registered in the interpreter extern table —
  `insert_simple!("rt_metal_create_device", gpu::rt_metal_create_device_fn)`
  (`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1136`), with the
  wrapper at `interpreter_extern/gpu.rs:878` and the codegen spec at
  `codegen/runtime_sffi.rs:1221`.
- The value is therefore a genuine `Value::Int(0)` returned by a real registered
  extern, **not** the silent-nil of an unregistered one. Same visible symptom,
  different mechanism, different fix. `unregistered_extern_silent_nil_2026-08-01`
  is not this bug.

The lane 4 record also left an open thread — "`MetalBackend.init` returns `true`
WITH zero pipelines, so there is a fail-open somewhere". **There is no such
fail-open on the device handle.** Both guards are present and correct:

- `metal_session.spl` init fails closed on `device_count <= 0`, then again on
  `self.device == 0` immediately after `metal_sffi_create_device(0)`.
- `metal_session.spl:161` fails closed on any zero pipeline handle (`last_error = 7`).
- `backend_metal.spl:426-438` fails closed on `session.init()` returning false.

The specs are correct device specs failing for a correct reason.

## Fix

**Fix side: build configuration, not source.** No Simple and no Rust behaviour
change was needed — the code was already right under the feature it was written
for. The seed is rebuilt into the same `CARGO_TARGET_DIR` with:

```
cargo build --release --bin simple \
    --features vulkan,metal,simple-compiler/vulkan-graphics
```

Note `vulkan-graphics` is a feature of the `simple-compiler` crate, **not** of
`simple-driver` which owns `[[bin]] name = "simple"` (`driver/Cargo.toml:15-17`),
so it must carry its package prefix on the command line. `metal` alone is the
whole Metal gate; there is no `metal-graphics` feature.

**Durable half.** The recurrence cause is that this feature list was codified
*nowhere*: `grep -rn "vulkan-graphics" scripts/ .github/ .claude/rules/ doc/07_guide/`
returned nothing, and the two `--features` occurrences under `scripts/bootstrap/`
and `scripts/setup/` concern `llvm` and `runtime-symbol-table` only. Any future
ad-hoc seed on macOS would repeat the mistake. Added
`scripts/setup/build-gpu-seed.shs`, which selects the GPU feature list by
`uname -s` and fails closed (exit 2) if no binary was produced.

## Measured evidence (2026-09-12, Apple M4)

Seed rebuilt in place, bracketed by `stat -f '%z %m'`:

| | size | mtime |
|---|---|---|
| before (`vulkan,vulkan-graphics`) | 39,368,072 | 1789171430 |
| after (`vulkan,metal,simple-compiler/vulkan-graphics`) | 39,178,424 | 1789197971 |

`cargo build --release --bin simple` finished in 5m39s warm, exit 0.

**Probe** (`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 … run`):

```
count=1
device=1        <- was device=0
```

**Spec** `test/02_integration/rendering/metal_msl_pipeline_spec.spl`:

```
7 examples, 0 failures
SPEC FILE VERDICT: ... outcome=OK declared>=7 executed=7 passed=7 failed=0
```
(was 7 examples / 5 failures). All five previously-failing examples — pipeline
creation, device glass dispatch, mirror-mode receipt rejection, and the 1d/2d
GPU dispatch dirty marks — pass on the real device.

**Rounded-rect corner AA, device pixel oracle at the arc.** A radius-4 rounded
rect filling a 16x16 Metal surface, read back with `read_pixels()` after
`use_gpu_only()`:

```
init=true  len=256
corner_0_0   = 4278190080  (0xff000000 — carved out by the arc)
corner_1_1   = 4294901760  (0xffff0000)
arc_4_4      = 4294901760  (0xffff0000 — arc centre, drawn)
centre_8_8   = 4294901760  (0xffff0000)
corner_15_15 = 4278190080  (0xff000000 — opposite corner, mirrors)
```
The corners are background and the interior is the fill colour, so the
`kernel_draw_rounded_rect` corner geometry really executed on the GPU — this is
a pixel value at the arc, not a compile check.

**Sabotage (red -> green -> red).** Forcing `metal_session.spl:133` to
`self.device = 0` reproduces the original signature exactly:

```
7 examples, 5 failures ... passed=2 failed=5
```
Reverting the line restores `7 examples, 0 failures`. The device handle is
therefore the single load-bearing variable.

## Newly exposed, NOT fixed here

`test/02_integration/rendering/metal_engine2d_readback_spec.spl` goes from
all-red (device 0) to **12 examples / 4 failures**. The remaining four are real
device-side defects that were previously masked by the dead device and are
**out of scope for this fix**:

- `downloads clear and rect_filled pixels from the Metal framebuffer`
- `stays GPU-complete after draw_text via the glyph-atlas kernel (GPU-dict #2, W4)`
- `blends a semi-transparent circle_filled identically on CPU mirror and Metal device (E1 fix)`
- `blends a semi-transparent triangle_filled identically on CPU mirror and Metal device (E2 fix)`

They need a separate cycle now that a device answers.
