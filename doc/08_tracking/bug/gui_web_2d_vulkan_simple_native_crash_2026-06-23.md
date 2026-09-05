# Bug: checked-in Simple native Vulkan evidence binary crashes

Status: mitigated for default wrapper; open for explicit `bin/simple_native`
Date: 2026-06-23
Area: GUI/web/2D Vulkan, Simple native evidence

## Symptom

On the linked worktree, explicit `SIMPLE_BIN=bin/simple_native
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run` crashes in the Simple
readback and Simple ARGB lanes:

```text
gui_web_2d_vulkan_simple_bin=bin/simple_native
gui_web_2d_vulkan_simple_bin_selection_reason=default-missing-same-repo-path-fallback
gui_web_2d_vulkan_simple_status=fail
gui_web_2d_vulkan_simple_reason=evidence-program-failed
gui_web_2d_vulkan_simple_argb_exit_code=139
gui_web_2d_vulkan_simple_argb_status=missing
```

The readback log records:

```text
check=vulkan_engine2d_readback
simple_bin=bin/simple_native
timeout: the monitored command dumped core
Segmentation fault
evidence_exit_code=139
overall=fail
```

## Required Evidence

The default wrapper path now avoids this stale binary by preferring
compiler-rust release/debug and same-repository PATH `simple` before checked-in wrappers. Full
closure of this blocker requires explicit `SIMPLE_BIN=bin/simple_native` to
produce:

- `gui_web_2d_vulkan_simple_status=pass`
- `gui_web_2d_vulkan_simple_backend_name=vulkan`
- `gui_web_2d_vulkan_simple_argb_status=pass`
- `gui_web_2d_vulkan_simple_argb_nonblank_pixel_count` greater than `0`
- `gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass`
- `gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass`
- `gui_web_2d_vulkan_pixel_comparison_status=pass`

Do not add raw `rt_*` shortcuts or fixture-only bypasses. Fix the Simple
compiler/runtime/backend owner path, refresh `bin/simple_native`, or keep using
a current non-crashing Simple binary through the existing `SIMPLE_BIN` override.
