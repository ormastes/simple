# Chrome 4K Showcase Baseline — 2026-09-05

## Result

The current macOS host produced a real Chrome headless screenshot of the canonical Overview tab at exactly 3840×2160. This is retained as a non-admitted cold reference; it is not evidence that Simple used Vulkan and is not a completed Chrome comparison receipt.

| Field | Evidence |
|---|---|
| Chrome executable | `/Applications/Google Chrome.app/Contents/MacOS/Google Chrome` |
| Fixture | `examples/06_io/ui/browser_common_elements_showcase.html`, Overview tab |
| Screenshot | `build/web_renderer_vulkan_4k_showcase_hardening/chrome/overview.png` |
| Dimensions | 3840×2160 PNG |
| Bytes | 131,185 |
| SHA-256 | `2244e432849e49a6c631939a7a7fcfe0ff59cae381788d8893bdbd8c31a94337` |
| Cold process-to-PNG wall time | 5.87 seconds |
| Process result | exit 0 |

Visual inspection confirmed the header, seven-tab navigation, selected Overview state, and Overview content. Chrome emitted `CVDisplayLinkCreateWithCGDisplay failed -6670` and an allocator warning, so GPU backend, presentation timing, warm p50/p95, dropped frames, and max RSS remain unverified. Consequently `comparison_admitted` must remain false.

The checked-in Chrome harness now builds its tab fixtures by injecting the same versioned typed inventory markup used by the Simple runner. The one-off screenshot above predates that shared-fixture correction and must not be used for pairwise pixel admission; regenerate all seven tabs through the harness when an admitted Simple runtime is available.
