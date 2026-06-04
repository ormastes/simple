<!-- codex-research -->
# WM Text Access MCP — Local Research

Date: 2026-06-01

## Question

Research whether the TRACE32 MCP pattern for text-accessible MDI windows can be generalized into a CLI/service/MCP layer that exposes host WM windows and UI items as text, then manipulates them through the same snapshot/query/action logic.

## Existing Local Pieces

### TRACE32 MCP precedent

- `examples/10_tooling/trace32_tools/t32_mcp/window_tools.spl` already models TRACE32 windows as cataloged text objects.
- The available handlers include `handle_t32_window_list`, `handle_t32_window_open`, `handle_t32_window_capture`, and `handle_t32_window_describe`.
- Window metadata is catalog-driven: `window_key`, title, kind, open command, capture command, capture mode, architecture, notes, actions, and fields.
- Capture uses explicit TRACE32 commands first. `WinPrint.*` is the primary path, with a `PRinTer.FILE` fallback when direct output is empty.
- `t32_setup_headless` and `t32_area_read` treat AREA windows as the stable headless text I/O channel. This is stronger than screen scraping because it uses TRACE32 semantics.
- Prior research in `doc/01_research/hardware/t32_mcp_cli_async_and_window_ux.md` recommends not building MCP status around transient GUI chrome. It prioritizes explicit state queries, capturable status windows, AREA output, and only then message-line text.

### Current packaged app gap

- `src/app/t32_mcp_server/main.spl` is currently a startup-light CLI/readiness surface for the packaged server. The richer tool implementation remains under `examples/10_tooling/trace32_tools/t32_mcp`.
- Any production WM text-access feature should either promote the example TRACE32 tool implementation into owned source or define a shared protocol that the example can target later.

### UI access protocol precedent

- `doc/02_requirements/feature/ui_access_protocol.md` selected a canonical access model for in-process Simple UI surfaces.
- Selected requirements include snapshots, surface-aware node IDs, recent events, actions, query/ensure/value tools, adapter snapshots, and visual probes.
- Important constraint from `doc/01_research/ui/ui_access_protocol.md`: v1 intentionally materializes from `UISession`, `UITree`, widget registry, and `SurfaceManager` rather than external OS accessibility APIs.
- This means WM text access should be a new adapter/source feeding the same access vocabulary, not a replacement for the existing in-process source of truth.

### WM automation precedent

- `src/lib/nogc_sync_mut/play/wm/mod.spl` already provides a shell-backed host WM surface:
  - `wm_screenshot`
  - `wm_list_windows`
  - `wm_focus_window`
  - `wm_click`
  - `wm_type_text`
  - `wm_press`
- Current backends are platform CLI based:
  - macOS: screenshots plus AppleScript/UI scripting helpers
  - Linux/X11: screenshot tools plus `xdotool`
  - Windows: PowerShell using Forms/Drawing for SendKeys and BitBlt screenshots
- This layer can focus and type into windows, but it does not expose a semantic text tree of controls/items.

### Shared WM renderer requirements

- `doc/02_requirements/feature/shared_wm_renderer_unification.md` requires host WM and SimpleOS WM to share lifecycle/routing logic for create, focus, move, resize, minimize, restore, close, and input routing.
- `doc/02_requirements/nfr/shared_wm_renderer_unification.md` requires WM parity and performance evidence.
- A WM text-access adapter must respect that boundary: common snapshot/query/action semantics above platform adapters; platform-specific accessibility/CLI details below.

## Local Gap Analysis

1. TRACE32 has semantic text windows because the application itself exposes command-driven windows, AREA, and `WinPrint`. Host WM windows do not uniformly expose that through `std.play.wm`.
2. Existing `std.play.wm` can enumerate and drive windows, but only at window/input/screenshot level.
3. Existing UI access can query/action semantic nodes, but only for in-process Simple UI surfaces.
4. There is no shared adapter contract that can normalize:
   - TRACE32 MDI windows
   - host OS windows
   - OS accessibility trees
   - Simple WM windows
   - screenshot/vision fallback marks
5. Hot-path warnings in AGENTS.md matter here: repeated full-tree scans, shell-outs, and retry sleeps in request handlers need explicit design and verification evidence.

## Recommended Local Shape

Add a `wm_text_access` adapter layer that emits canonical UI access snapshots from multiple sources:

- `trace32_window_adapter`: catalog + `WinPrint` + AREA + action templates.
- `host_wm_adapter`: `std.play.wm` window list/focus/input as the minimum window-level source.
- `host_accessibility_adapter`: Windows UIA, macOS AX, Linux AT-SPI when available.
- `simple_wm_adapter`: SimpleOS/host WM service state when the target is owned by Simple.
- `vision_fallback_adapter`: screenshot-derived marks only as a lower-confidence sidecar.

The shared logic should live above adapters:

- snapshot normalization
- stable IDs
- query/find/filter
- action routing
- value read/write where supported
- recent event/history
- CLI/service/MCP schemas

## Risks

- Host accessibility APIs vary heavily by OS and app toolkit.
- Wayland limits global window control; AT-SPI can expose semantic trees but not compositor-level control for every app.
- Shell-backed WM calls are useful for smoke automation but too expensive for hot request paths unless cached and explicitly invalidated.
- Screenshot-only fallback cannot reliably manipulate MDI controls by text without semantic anchors.

## Conclusion

The TRACE32 MCP pattern is a good model for adapter-backed text access, but only because TRACE32 provides semantic command windows. The general solution should not scrape every GUI as text. It should define a shared canonical access protocol, then let each adapter expose the strongest available semantic source: TRACE32 commands, Simple UI session state, OS accessibility APIs, or basic WM window/input controls.

