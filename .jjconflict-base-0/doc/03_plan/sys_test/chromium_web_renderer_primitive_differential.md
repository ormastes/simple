# Chromium Web Renderer Primitive Differential — System Test Plan

| REQ | Scenario/helper | Evidence and required assertion |
|---|---|---|
| REQ-CWP-001 | `load_validated_chromium_plugin` | Explicit ABI v1, hash, all symbols, compiled mode; no synthetic trace. |
| REQ-CWP-002 | `compare_rect_border_cpu_pixels` | DOM/style/layout/paint trace and exact Simple CPU RGBA8 result. |
| REQ-CWP-003 | `compare_text_font_metrics` | Font/text/baseline metrics plus exact CPU pixels. |
| REQ-CWP-004 | `compare_image_placement` | Resource digest, intrinsic size, placement, paint ordering and pixels. |
| REQ-CWP-005 | `dispatch_pointer_ctrl_alt_events` | Target/default action/focus and left/right Ctrl/Alt facts, not dispatch acknowledgement. |
| REQ-CWP-006 | `compare_scroll_resize_post_state` | Scroll offset, viewport and affected layout boxes. |
| REQ-CWP-007 | `gate_linear_path_capability` | Both sides support and compare, or explicit `unsupported-primitive`. |
| REQ-CWP-008 | `assert_simple_vulkan_readback` | Submit/fence/device identity/device readback digest/no fallback under admitted profile. |
| REQ-CWP-009 | `reject_oracle_mutations` | One-field mutations and loader/ownership/order/budget malformed paths reject. |

The eventual spec uses `step("Load validated Chromium primitive oracle")`,
`step("Run normalized primitive fixture")`,
`step("Compare semantic stages and CPU pixels")`, and
`step("Require device readback without fallback")`. Until the native bridge is
present, every helper must fail explicitly with `fail("Chromium primitive oracle
not installed")`; it may not leave a passing placeholder. Capture kinds are
`protocol` for normalized trace, `artifact` for manifest/readback, and `gui`
only as supplemental human review evidence.
