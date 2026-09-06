# Sdl Present Failure Contract Specification

> Tests covering SDL presentation failure contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdl Present Failure Contract Specification

## Scenarios

### SDL presentation failure contract

#### returns actual runtime blit and update success

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns actual runtime blit and update success
   - Expected: runtime does not contain `#include <SDL.h>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns actual runtime blit and update success")
val header = rt_file_read_text("src/runtime/runtime.h") ?? ""
val runtime = rt_file_read_text("src/runtime/runtime_sdl2.c") ?? ""

# runtime_sdl2.c loads SDL2 dynamically (dlopen/LoadLibrary) by design —
# it must NOT include SDL headers; assert the dynamic-load contract instead.
expect(runtime).to_contain("dlopen(name, RTLD_NOW | RTLD_LOCAL)")
expect(runtime.contains("#include <SDL.h>")).to_equal(false)
expect(header).to_contain("bool     rt_sdl2_present_rgba")
expect(header).to_contain("bool     rt_sdl_present_rgba")
expect(runtime).to_contain("if (window_handle == 0 || !pixels) return false;")
expect(runtime).to_contain("if (width > INT_MAX / 4 || height > INT_MAX) return false;")
expect(runtime).to_contain("if (SDL_BlitScaled(src, NULL, dst, &dst_rect) == 0)")
expect(runtime).to_contain("presented = SDL_UpdateWindowSurface(win) == 0;")
expect(runtime).to_contain("return presented;")
```

</details>

#### does not replace SDL failure with unconditional success

- does not replace SDL failure with unconditional success


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not replace SDL failure with unconditional success")
val app_ffi = rt_file_read_text("src/app/io/window_ffi.spl") ?? ""
val app_sffi = rt_file_read_text("src/app/io/window_sffi.spl") ?? ""
val lib_sffi = rt_file_read_text("src/lib/nogc_sync_mut/io/window_sffi.spl") ?? ""

expect(app_ffi).to_contain("export use app.io.window_sffi.")
expect(app_ffi).to_not_contain("extern fn rt_sdl2_present_rgba")
expect(app_sffi).to_contain("export use std.nogc_sync_mut.io.window_sffi.")
expect(app_sffi).to_not_contain("extern fn rt_sdl2_present_rgba")
expect(lib_sffi).to_contain("extern fn rt_sdl2_present_rgba(window_handle: i64, pixels: [i64], width: i64, height: i64) -> bool")
expect(app_ffi).to_not_contain("rt_sdl2_present_rgba(window.handle, pixels, width, height)\n        true")
expect(app_sffi).to_not_contain("rt_sdl2_present_rgba(window.handle, pixels, width, height)\n        true")
expect(lib_sffi).to_not_contain("rt_sdl2_present_rgba(window.handle, pixels, width, height)\n        true")
```

</details>

#### stops WebUI and exposes editor presentation failure

- stops WebUI and exposes editor presentation failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stops WebUI and exposes editor presentation failure")
val web_window = rt_file_read_text("src/lib/nogc_sync_mut/web_ui/window.spl") ?? ""
val web_app = rt_file_read_text("src/lib/nogc_sync_mut/web_ui/app.spl") ?? ""
val editor = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""

expect(web_window).to_contain("me present() -> bool:")
expect(web_window).to_contain("if not w.present():\n                return false")
expect(web_app).to_contain("if not self.window_manager.present_all():")
expect(web_app).to_contain("presentation_ok = false\n                self.running = false")
expect(editor).to_contain("extern fn rt_sdl_present_rgba(window_handle: i64, pixels: [i64], width: i64, height: i64) -> bool")
expect(editor).to_contain("fn gui_sdl_present_frame(window: i64, frame: GuiFrame) -> bool:")
```

</details>

<details>
<summary>Advanced: stops browser and engine loops after presentation failure</summary>

#### stops browser and engine loops after presentation failure

- stops browser and engine loops after presentation failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stops browser and engine loops after presentation failure")
val browser = rt_file_read_text("src/app/ui.browser/app.spl") ?? ""
val loop2d = rt_file_read_text("src/lib/nogc_sync_mut/engine/core/game_loop.spl") ?? ""
val loop3d = rt_file_read_text("src/lib/nogc_sync_mut/engine/core/game_loop3d.spl") ?? ""

expect(browser).to_contain("fn browser_winit_window_present_rgba(win: i64, w: i64, h: i64, pixels: [i64]) -> bool:")
expect(browser).to_contain("if not self.present_host_window(window):\n            print \"Error: failed to present initial browser frame\"")
expect(browser).to_contain("presentation_ok = false\n                    self.running = false")
expect(browser).to_contain("if app.run():\n                return 0\n            return 1")

expect(loop2d).to_contain("presentation_failed: bool")
expect(loop2d).to_contain("val presented = window_present_rgba(")
expect(loop2d).to_contain("self.presentation_failed = true\n                            self.running = false")
expect(loop2d).to_contain("not self.presentation_failed")

expect(loop3d).to_contain("presentation_failed: bool")
expect(loop3d).to_contain("val presented = window_present_rgba(")
expect(loop3d).to_contain("self.presentation_failed = true\n                    self.running = false")
expect(loop3d).to_contain("not self.presentation_failed")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/sdl_present_failure_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDL presentation failure contract.
- SDL presentation failure contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e5df6790ebabdcfcf8cf8d9c4e92bc95d1f041d1ef9c0ab693a23d0e863fd4e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5df6790ebabdcfcf8cf8d9c4e92bc95d1f041d1ef9c0ab693a23d0e863fd4e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5df6790ebabdcfcf8cf8d9c4e92bc95d1f041d1ef9c0ab693a23d0e863fd4e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/rendering/sdl_present_failure_contract_spec.spl
mirror: doc/06_spec/02_integration/rendering/sdl_present_failure_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/sdl_present_failure_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/sdl_present_failure_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/sdl_present_failure_contract_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns actual runtime blit and update success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/sdl_present_failure_contract_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not replace SDL failure with unconditional success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/sdl_present_failure_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stops WebUI and exposes editor presentation failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
