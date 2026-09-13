# GPU seed capability drift was a stale binary, not a missing cargo feature (2026-09-12)

## Claim under test

F23 reported that `/Users/ormastes/simple/build/cargo-r2/release/simple`
(F26's rebuild with `--features vulkan,metal,simple-compiler/vulkan-graphics`)
"lacks `rt_vulkan_copy_to_buffer_u32`", implying the typed-upload / native
-readback lanes (`SIMPLE_VK_RECT_UPLOAD=u32`, `SIMPLE_VK_IMAGE_UPLOAD=u32`,
`SIMPLE_VK_READBACK=native`) were silently broken by an incomplete feature
list in `scripts/setup/build-gpu-seed.shs`.

## What was actually true

The feature graph was already correct. Reading it directly:

- `src/compiler_rust/driver/Cargo.toml`: `vulkan = ["simple-compiler/vulkan"]`,
  `metal = ["simple-compiler/metal"]`.
- `src/compiler_rust/compiler/Cargo.toml`: `vulkan = [..., "simple-runtime/vulkan"]`,
  `metal = ["simple-runtime/metal"]`.

So the script's `vulkan,metal,simple-compiler/vulkan-graphics` feature list
already turns on `simple-runtime/vulkan` and `simple-runtime/metal`, which is
the whole gate for the real (non-stub) `rt_vulkan_*` / `rt_metal_*`
definitions in `runtime/src/vulkan_graphics_runtime_buffer.rs` and
`runtime/src/metal_graphics_runtime.rs`. The interpreter-side dispatch table
(`compiler/src/interpreter_extern/mod.rs::init_dispatch_table`, consulted at
`call_extern_function_with_values` line ~3203) registers
`rt_vulkan_copy_to_buffer_u32` and `rt_vulkan_readback_u32_array`
unconditionally — no `#[cfg(feature = ...)]` gates either registration.

**Ground truth, measured directly against the deployed binary**
(`stat -f '%z %m'` = `39178424 1789197971`, sha256
`d7b9878102b1998c5ef1fafb15610860d427e767f6fa3aaa0e8d7d39273e1eda`):

```
$ strings -a "$S" | grep -c rt_vulkan_copy_to_buffer_u32
0
$ strings -a "$S" | grep -c rt_vulkan_readback_u32_array
0
$ strings -a "$S" | grep -c rt_vulkan_alloc_buffer
7
```

The binary genuinely did not contain either symbol name as a string
constant, while a neighboring, older `rt_vulkan_*` symbol (`rt_vulkan_alloc_buffer`)
was present 7 times. `git log -S "rt_vulkan_copy_to_buffer_u32" -- .../interpreter_extern/mod.rs`
shows the registration landed in commit `17aec7247b6` ("perf(gpu): typed
[u32] rect-batch upload; prove one submit per frame", 2026-09-11), and the
readback registration landed in `22e759e9757` the same day. **The deployed
binary predates one or both of those commits** — it was built from an older
tree, most likely by a session other than the one that ran the last
`build-gpu-seed.shs` invocation, consistent with this repo's
`feedback_harvest_dead_agent_worktree` / "3 distinct builds seen in one
session" observation about `bin/simple`'s symlink target being replaced
mid-session by concurrent agents.

**Conclusion: this was binary-identity drift (a stale artifact at the shared
build path), not a cargo-feature gap.** No feature-list change was needed or
made.

## Probes run (interpreter mode, `SIMPLE_TIMEOUT_SECONDS=0`)

Against the stale binary (before rebuild):

| spec | env | result |
|---|---|---|
| `backend_vulkan_rect_batch_typed_upload_spec.spl` | `SIMPLE_VK_RECT_UPLOAD=u32` | 8 examples, 6 failures — `unknown extern function: rt_vulkan_copy_to_buffer_u32` |
| `backend_vulkan_image_typed_upload_spec.spl` | `SIMPLE_VK_IMAGE_UPLOAD=u32` | 7 examples, 6 failures — same extern |
| `engine2d_vulkan_readback_unpack_cost_spec.spl` | `SIMPLE_VK_READBACK=native` | 2 examples, 2 failures — `unknown extern function: rt_vulkan_readback_u32_array` |
| `metal_msl_pipeline_spec.spl` | — | 7 examples, 0 failures |
| `wffi_into_bytes_spec.spl` | — | 5 examples, 5 failures — `panic: E-SFFI-001: failed to load provider: empty provider path` (unrelated: `build/chrome-render/libsimple_chrome_render.{dylib,so}` shim was not yet built in this working tree; fixed by running `sh scripts/check/build-chrome-render-shim.shs` once, not a seed-feature issue) |

After rebuilding the seed from current `HEAD` (`202b68dd665`) into the same
target dir `/Users/ormastes/simple/build/cargo-r2` with the **unchanged**
feature list `vulkan,metal,simple-compiler/vulkan-graphics`:

| spec | env | result |
|---|---|---|
| `backend_vulkan_rect_batch_typed_upload_spec.spl` | `SIMPLE_VK_RECT_UPLOAD=u32` | 8 examples, 0 failures |
| `backend_vulkan_image_typed_upload_spec.spl` | `SIMPLE_VK_IMAGE_UPLOAD=u32` | 7 examples, 0 failures |
| `engine2d_vulkan_readback_unpack_cost_spec.spl` | `SIMPLE_VK_READBACK=native` | 2 examples, 0 failures |
| `metal_msl_pipeline_spec.spl` | — | 7 examples, 0 failures |
| `wffi_into_bytes_spec.spl` | — | 5 examples, 0 failures |

New binary: `39528776` bytes, mtime `1789199850`, sha256
`606d464fee80a9576a6d4cc7bfa388582992f2aa2e6a212143041a15d6fbce94`.

## Fix landed

`scripts/setup/build-gpu-seed.shs` gained a `--verify [seed-path]` mode that
runs exactly the five probes above (`SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0 <seed> run <spec>`, from the repo root) and reports
a fail-closed verdict:

- `PASS — <n> capability probe(s) executed` (exit 0)
- `FAIL — <spec>(unknown-extern:<symbol>|rc=<n>:<verdict-line>) ...` (exit 1)
- `ERROR — nothing was checked (...)` (exit 2) when the seed path is not
  executable or 0 probes ran

A normal build run now also calls the same probe set against what it just
built and prints a `WARNING` (with the FAIL/ERROR verdict) if verification
does not pass, without failing the build itself — the artifact still gets
deployed, but drift is surfaced immediately instead of silently.

`--selftest` (4 fixtures, run automatically at the start of `--verify`) covers:
a fake seed that emits `N examples, 0 failures` (must PASS), one that emits
`unknown extern function: <symbol>` (must FAIL, naming the symbol), one that
exits non-zero with no extern-not-found text (must FAIL), and a nonexistent
seed path (must ERROR).

## Why "read the feature graph" alone was not enough here

The feature-graph reasoning correctly proved the *build configuration* was
sufficient; it could not detect that the *specific binary on disk* was built
from an older tree. Only calling the binary (or diffing `strings` output
against `git log -S`) surfaces that distinction — which is the reason
`--verify` exists as an executable check rather than a documentation note.
