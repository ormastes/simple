<!-- codex-design -->
# Tiny UI/Web/WM architecture

Date: 2026-08-14
Status: proposed implementation architecture

## Principal architecture

```text
Tiny TUI (host oracle) ----\
Tiny Web -> Tiny GUI -------+-> TinyPane -> TinyDrawStream -> Tiny 2D -> Tiny WM
Tiny Lib ------------------/                         \-> Tiny Vulkan    |
                                                                      v
                                                        host/SimpleOS present
                                                                      |
                                                        RV32 fullscreen browser
```

Tiny WM is the boundary that turns the renderer into a complete embedded product. It owns surface admission, root/popup policy, focus/capture, damage, composition choice, and presentation. It is a strict shared-WM profile, never a second web-only semantic authority.

## Normative upstream contracts

- Shared widget/event semantics: `doc/04_architecture/ui/shared_ui_contract.md`.
- Shared WM ownership and renderer rules: `doc/04_architecture/os/shared_wm_stack.md` and `shared_wm_renderer_unification.md`.
- Dependency classification: `doc/04_architecture/ui/wm_gui_web_dependency_audit.md`.
- Canonical full browser engine oracle: `doc/04_architecture/adr/ADR-002-canonical-browser-engine.md`.
- Existing low-dependency dynSMF design: `doc/04_architecture/ui/low_dependency_ui_dynsmf.md`.

## MDSOC+ placement

- `tiny_browser` is an application capsule whose internal retained/ECS state owns page, focus, scroll, and navigation state.
- `tiny_wm` is either a linked capsule or service capsule with identical ports and systems. The linked transform removes IPC in the smallest profile.
- Tiny Web is a bounded parsing/layout domain capsule.
- Tiny 2D is an execution port with software and optional Vulkan implementations.
- display/input drivers are MDSOC ports and contain no application ECS.

## Frozen interfaces

`TinyModuleV1`, `TinyRect`, `TinyPane`, `TinyEvent`, `TinyDrawStreamV1`, `TinyRenderedSurfaceV1`, `TinyWebHostPortV1`, `Tiny2DBackendV1`, `TinyWmPortV1`, `TinyPresentPortV1`, and `TinyInputPortV1` are Wave-0 contract-owner surfaces. `Tiny2DBackendV1` consumes the versioned draw envelope and exposes a rendered-surface receipt; `TinyPresentPortV1` presents that exact receipt after damage admission. Raw command words and damage-only presentation are internal/legacy shapes, not the Tiny V1 boundary.

Simple-facing APIs retain wrapper types. Only the explicit serialized/dynamic ABI boundary uses numeric POD fields and codecs.

## Relative-pane invariant

```text
absolute_origin = parent.absolute_origin + pane.local_origin - parent.scroll_offset
effective_clip  = intersect(parent.effective_clip, pane.absolute_bounds)
local_hit_point = screen_point - pane.absolute_origin
```

Paint walks children in stable z/order with translate and clip stacks. Hit testing walks the same resolved geometry in reverse paint order.

## Render protocol decision

TinyDrawStream is a compact validated execution encoding. Full DrawIR remains the canonical inspection/interchange capability for the full stack. Adapters must prove representability in both directions; unsupported full commands fail explicitly.

Base operations are frame begin/end, clip push/pop, translate push/pop, rectangle fill/border, horizontal/vertical line, bitmap glyph run, and bitmap blit. Optional layers, paths, gradients, and alpha commands live in packs.

## Tiny WM policy

The base contains one output, one fullscreen opaque root, bounded popups, keyboard/pointer focus, capture, hierarchical clipping, bounded damage, direct opaque presentation, and optional software cursor. Desktop windows, chrome, taskbar, workspaces, multi-output, effects, remote IPC, and generalized service discovery are optional.

Weston kiosk shell is precedent for separating fullscreen kiosk policy from reusable compositor machinery; it is not evidence for this exact one-root contract.

The linked browser retains one `TinyWmKiosk` owner. Mutable WM/present operations execute on that retained owner rather than on copied class values; frame receipts are read from the same owner after root admission. Direct present is true only when the sole visible root is opaque and its resolved origin and extent exactly equal the output. This owner/result invariant is covered at the isolated WM and integrated browser boundaries.

## Module architecture

Every class is addressable, but embedded deployment groups classes into feature packs. Static and dynamic builds consume the same versioned descriptor. Static registration enables LTO/section collection; dynamic loading uses current SFM/dynSMF through a thin adapter. The proposed facet-pack runtime is a future adapter, not a dependency.

The existing low-dependency dynSMF defaults are not changed. A separate tiny profile declares its measured mandatory pack set.

## Data and dependency direction

```text
browser -> web/gui -> pane/event -> draw -> 2d backend
                                      \------> wm content port -> wm -> present/input
optional adapter -----------------------------> public tiny port
tiny core -X-> optional implementation
```

Host adapters, full UI/Web/WM modules, diagnostics, DrawIR/WebIR adapters, and Vulkan cannot be imported by the base RV32 closure.

## Failure and observability

All boundaries return numeric typed results for capacity, ABI, malformed input, unsupported command, missing capability, invalid handle, device loss, and presentation failure. Host/debug packs translate IDs to prose. Evidence records arena high-water, parser budgets, command counts, damage merge reasons, backend identity, frame checksum, timings, sections, symbols, and dependency closure.

## Architecture acceptance

Acceptance requires dependency gates proving no full-stack leakage, static/dynamic capability parity, identical pane resolution for render/hit paths, strict backend selection, host nested-pane/browser evidence, staged RV32 boot/framebuffer/input evidence, and the 409,600-byte gates.
