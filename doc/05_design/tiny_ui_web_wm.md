<!-- codex-design -->
# Tiny UI/Web/WM detail design

## Core records

- `TinyPane`: generational ID/parent, local rectangle, local clip, scroll, bounded z, flags, content handle.
- `TinyEvent`: tagged keyboard, text, pointer, wheel, focus, action, resize, and frame events with integer payloads.
- `TinyModuleV1`: ABI versions, feature/module IDs, capabilities, class table, init/shutdown/query/create/destroy entries.
- `TinyRenderedSurfaceV1`: ABI/capability identity, stable surface/frame IDs, dimensions, pixel format, exact pixels/readback source, and checksum passed from Tiny 2D to presentation.
- `TinySurface`: parent, local bounds, effective clip, content handle, z, opacity, flags, and bounded damage reference.
- `TinyDocument`: indexed node/style/layout arenas and bounded text pool.

No GC handles, general dictionaries, exceptions, implementation object layouts, or unbounded text cross module ABIs.

## Base component semantics

Pane, Row, Column, Stack, Text, Spacer, Divider, Border, Button, Checkbox, TextInput, List, ScrollPane, and Progress share TinyPane geometry and TinyEvent dispatch. Image, Radio, Dropdown, Tabs, Dialog, Table, Tree, Slider, Canvas, Animation, RichText, terminal extensions, and accessibility export are packs.

## Tiny Web

The pipeline is bounded tokenizer/tree builder -> CSS token/rule arena -> computed style -> block/inline layout -> hit index -> TinyDrawStream. Initial tags and properties are those in REQ-005. Every configured byte, node, depth, attribute, rule, selector-part, text-pool, and command limit returns a receipt on exhaustion.

Resources default to built-in page, ROM, or VFS through the frozen `TinyWebHostPortV1`. External fetch and TLS are separate services/packs. The initial source snapshot does not yet implement or bind that port; `tiny_resource_request` only validates caller-supplied metadata and is not accepted product evidence.

## Tiny 2D

The software backend supports RGB565 and ARGB8888, integer clip/translate, clear/fill/border, bitmap glyphs, bitmap blit, bounded damage, and tile/scanline or direct output rendering. A compact built-in bitmap font avoids parsers and shaping. Software output is the pixel oracle.

Tiny Vulkan implements `Tiny2DBackendV1` as a client of an existing loader/driver or OS GPU service. It embeds prebuilt shader data only and fails closed in strict mode. Every backend consumes `TinyDrawStreamV1` and returns `TinyRenderedSurfaceV1`; present validates the same surface/frame/checksum identity instead of accepting a damage-only success receipt.

## Tiny WM systems

`resolve_surface_geometry`, `admit_kiosk_root`, `place_popup`, `route_input`, `merge_damage`, `select_direct_present`, `compose_surfaces`, `present_frame`, and `retire_destroyed_surfaces` operate over bounded components.

The accepted design uses a preallocated fixed-capacity rectangle store with a separate logical count. Intersecting/near rectangles merge; overflow collapses to a bounding rectangle; configured coverage triggers a full redraw with a reason code. Direct present requires one opaque output-sized root and no intersecting software popup/cursor. WM damage/present/input source now uses fixed backing stores and logical counts, but executable allocation evidence remains required. Web and GUI transient arenas still grow arrays after browser initialization and therefore do not yet satisfy this design or NFR-011; see blocker B-14.

## Browser flow

Boot/launch -> initialize bounded arenas and static registry -> bind resource/input/present ports -> create fullscreen root -> parse built-in/VFS page -> resolve pane tree -> emit/validate draw stream -> software render -> Tiny WM present -> poll and route events -> update focused control/scroll/navigation -> damage repaint.

`TinyBrowser` is the mutation owner for retained renderer, WM, GUI, present, and scroll values. It calls mutable WM/present methods directly on its fields. Interaction-only setup admits the fullscreen root before keyboard/text dispatch. Pointer/wheel events route through Tiny WM first; accepted wheel input then applies `tiny_scroll_by` and returns the resulting typed change receipt. A copied-owner mutation followed by assignment is not a valid integration path.

## Initial planning budgets

| Area | KiB |
|---|---:|
| runtime/startup | 48 |
| Tiny Lib/registry | 34 |
| Tiny Web | 96 |
| GUI/panes/events | 28 |
| Draw/2D/font | 62 |
| WM/input/present | 26 |
| browser shell/page | 20 |
| metadata/constants | 18 |
| subtotal/reserve | 332 / 68 |

Budgets are hypotheses until the empty-RV32 and vertical-slice maps exist.

## Repository placement

Use `src/lib/nogc_sync_mut/tiny/{common,pane,gui,draw,engine2d,web,tui,wm_contract,compat}` for reusable code, `src/os/services/tiny_wm` for linked/service capsule and aspects, `src/os/apps/tiny_browser` for the embedded application, and host apps only for TUI/browser oracle execution.

## Compatibility generation

One `tiny_component_map.sdn` generates aliases, static registry, SFM entries, docs, capability matrix, fixture parameters, and export allowlist. Each row records legacy/tiny names, IDs, status, packs, adapters, semantic differences, and fixtures.
