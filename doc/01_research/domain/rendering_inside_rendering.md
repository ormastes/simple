# Rendering Inside Rendering: Nested/Embedded Render Surfaces

Research for a pure-Simple stack: 2D renderer (CPU + Metal) + web renderer (own
HTML/CSS/JS engine) + GUI toolkit/WM/compositor, needing (1) 2D offscreen/embedded
render targets, (2) iframe-like web-in-web with per-instance isolated "space" by
default (optionally shared), (3) GUI panels embedding GUI/web panels, (4) possible
3D scene-in-scene.

## 1. Browsers / Chromium

**Mechanism.** An `<iframe>` creates a nested *browsing context*. Cross-site
iframes are, under Site Isolation, rendered out-of-process (OOPIF): the child
frame runs in its own renderer process with its own compositor, and the parent
only holds a placeholder (`RenderFrameProxy`). Each renderer produces its own
`CompositorFrame`; these are **not drawn into the parent's paint/command
stream**. Instead, the child renderer submits a frame to a `viz::Surface`
identified by a `SurfaceId`, and the parent embeds a `cc::SurfaceLayer`
referencing that `SurfaceId` in its own layer tree. The privileged **viz**
process (GPU process) runs a `SurfaceAggregator` that walks the tree of
surfaces, substitutes each `SurfaceLayer` draw-quad with the referenced
child's `CompositorFrame` content, culls offscreen/occluded content, and
composites everything into one final frame for the OS window. This is the key
architectural move: **composition/aggregation happens below and outside any
single renderer**, as a tree-of-surfaces resolved by a dedicated compositor.

**Isolation boundaries.**
- *Process*: Site Isolation puts different-site frames in different OS
  processes; a "site instance" groups documents that must share synchronous
  access (same-origin scripting).
- *Script/space*: a **browsing context group** is the set of contexts that can
  reach each other synchronously (`window.opener`, `frames[0]`, shared
  `SharedArrayBuffer` via an *agent cluster*). Same-origin iframes in the same
  tab are, by default, **site-keyed** into a shared agent cluster (can see/touch
  each other via the DOM); `Origin-Agent-Cluster` header can request finer,
  origin-keyed isolation even within the same site. Cross-origin iframes are
  always separate script realms (separate `window`/global) regardless of
  process — the *shared-vs-separate-space* switch in the web platform is really
  two independent axes: (a) same-agent-cluster (memory/thread sharing,
  requester-controlled via headers) and (b) same-origin (script/DOM access,
  origin-controlled, cannot be widened by the embedder).
- *Coordinates/damage*: each surface has its own device-pixel coordinate space
  and its own damage/invalidation tracking; the aggregator translates child
  quad rects into parent space and only re-aggregates the regions that
  changed (damage rects propagate up the surface tree, not full repaints).
- *Lifecycle*: a `SurfaceId` embeds a "local surface id" that increments per
  commit, so the parent can keep displaying the *last* good frame from a
  crashed/slow child (frame is independent and revisable) — this is what makes
  a hung iframe not blank the rest of the page.

**Input routing.** Hit-testing walks the surface/frame tree using the
aggregated geometry (viz keeps a `HitTestQuery` per surface); an event's
screen point is resolved to the deepest owning `RenderFrameProxy`/frame, and
the OS-level input event is then routed (via IPC) directly to that frame's own
renderer process, in its local coordinate space (after subtracting the
iframe's offset + any CSS transforms).

**Electron's variants** (useful as "what a UI toolkit built on a browser
engine does"): `<webview>` = OOPIF-backed custom element with shadow DOM,
separate process, discouraged now due to security/perf edge cases;
`BrowserView`/`WebContentsView` (its successor, built on Chromium's own Views
API) = an explicit child `WebContents` positioned by the *host process* as a
rectangle over/within a `BrowserWindow`, not a DOM node at all — i.e. it lives
at the **window-compositor layer**, not the **web-layout layer**. This is a
second valid nesting *level*: embed a whole renderer as a native panel rather
than as a DOM element.

## 2. Wayland subsurfaces / X11 XEmbed

**Wayland `wl_subcompositor` / `wl_subsurface`.** A subsurface is a full
independent `wl_surface` (own buffer, own client, potentially own process)
positioned relative to a parent surface, arranged in a tree with stacking
order. Each subsurface owns its own commit/damage lifecycle, but has a
**sync/desync mode**: in *synchronized* mode (the default), a subsurface's
committed state is cached and only applied atomically when the *parent*
commits — guaranteeing the parent and child never show a torn combination of
old/new content. In *desynchronized* mode the child can update independently
(e.g. a video overlay running at its own frame rate). Sync/desync is
recursive: a desynced child under a still-synced parent still waits on that
parent. Position/z-order changes are always buffered with the parent's
commit regardless of mode. This maps closely onto "does the child repaint
freely or only in lockstep with the parent's frame" — directly relevant to
our WM panel-in-panel damage model.

**X11 XEmbed.** Older, more manual: reparents the child's X window into the
embedder (embedder acts as a mini window-manager for it). Since X input focus
is global and singular, the protocol's trick is a **focus proxy**: the
top-level embedder keeps real X input focus on an invisible 1x1 proxy window
it owns, and forwards key events to the logically-focused embedded window by
rewriting the event's target window and resending via `XSendEvent` (with
propagation disabled) — i.e. **input is intercepted at the top and
re-dispatched down the tree**, rather than the OS routing it directly to the
nested window. Client messages (`XEMBED_FOCUS_IN/OUT`, activate/deactivate)
tell the child when it logically has focus so it can draw a focus ring, etc.
Relevant lesson: whoever owns the real input source must be a single owner at
the root, with an explicit protocol to hand focus down.

## 3. GPU / compositor layer models

- **Render-to-texture / FBO**: the universal primitive — a child renders its
  content into an offscreen color (+depth/stencil) buffer instead of the
  default framebuffer; the buffer is then sampled as a texture by whoever
  draws the parent scene. This is what "own render surface" bottoms out to on
  a GPU, in Metal terms: a child `MTLRenderPassDescriptor` targeting an
  `MTLTexture` (usable both as 2D-in-2D and as a texture on a 3D quad/mesh).
- **Layer trees (Core Animation / Chromium cc-viz / Wayland)**: universally,
  systems that need nesting converge on a **retained tree of surfaces/layers**
  with per-node transform, opacity, clip, and independent
  damage/invalidation — composition is a separate pass from painting content.
- **WebRender (Firefox) picture caching**: tags stable, axis-aligned
  "pictures" (e.g., a scrollable subframe, an iframe's content) as cacheable
  tiles; if a picture's inputs haven't changed, the compositor reuses the
  cached tiles instead of repainting, and only the picture's tile *and* the
  final composite handle the parent/child boundary — i.e. the nested render
  target is explicitly the unit of caching, not just of isolation.

## 4. UI toolkits

- **Flutter platform views**: three generations show the trade space plainly.
  *Virtual Display* (old): native view renders into an off-screen
  `SurfaceTexture`-backed virtual display, cheap for Flutter's compositor but
  each pixel flows through extra GPU buffers and some native input/a11y
  features degraded. *Hybrid Composition* (real native view in the actual
  Android view hierarchy, interleaved with Flutter layers via `SurfaceView`
  splitting) — correct behavior but costly `SurfaceView` synchronization.
  *Texture Layer Hybrid Composition* (current default, Flutter 3+): the native
  view still lives in the real native view hierarchy (so input/a11y/IME work
  correctly) but is drawn into a `Canvas` that backs a Flutter `Texture`,
  which Flutter's own compositor then composites like any other layer — no
  `SurfaceView`, no copy-through-main-memory. Net lesson: **the best model
  keeps the child's *event/accessibility* identity in the native/host tree
  while its *pixels* flow through a texture handoff into the parent's
  compositor**, rather than picking only one of pixel-path or event-path.
- **Qt `QQuickRenderControl`**: renders an entire QtQuick scene graph off
  the normal windowing path into an app-supplied texture/FBO — this is the
  purest "render subsystem into a texture I own and place myself" API, and is
  the closest single-process analogue to what our 2D-renderer-embeds-2D-scene
  feature needs. Caveat found while embedding a `QWebEngineView` inside a
  `QQuickRenderControl`-driven scene: Chromium's GPU process/context is
  process-global and not exposed for sharing by default, so nesting a
  "different rendering subsystem" inside a custom offscreen render loop needs
  an explicit shared-GL-context hookup — a warning for us: our web-renderer's
  GPU context and our 2D-renderer's GPU context need a designed sharing/handoff
  contract, not an assumption it "just composites."
- **GTK offscreen windows** (`GtkOffscreenWindow`, legacy) and **Electron
  BrowserView/WebContentsView**: both confirm the "embed a whole native
  panel/renderer as a rectangle positioned by the host, independent of the
  document tree" pattern — this is the model for "GUI panel embeds a whole
  web-panel or another GUI subtree" in our WM layer, as distinct from
  "iframe embedded inside HTML layout."

## 5. Game engines — scene-in-scene

- **Godot `SubViewport`**: the closest existing model to what we're building
  system-wide. A `SubViewport` is a node in the scene tree that renders its
  *own subtree* to a texture (`ViewportTexture`), consumable by a
  `TextureRect`/sprite/3D quad elsewhere in the (same or different) scene.
  Key switch: **`own_world_3d` / world sharing**. By default a `SubViewport`
  can either use its parent viewport's `World3D`/`World2D` (objects are
  literally shared/visible in both, e.g. a security-camera view of the *same*
  live world) or set its own world so its subtree is a fully separate physics
  /rendering universe (e.g. a character-portrait renderer with its own lit
  scene) — this single boolean is exactly the "separate vs shared space"
  toggle our spec calls for. It also has an explicit **update mode**
  (`Always` / `Once` / `WhenVisible` / `Never`) — a damage/redraw-scheduling
  knob analogous to Wayland's sync/desync.
- **Unity `RenderTexture`**: a camera renders into a `RenderTexture` asset
  instead of the screen; that texture is then applied as a material anywhere
  (minimap, portal, mirror, security monitor, UI raw image). No built-in
  "shared vs separate world" flag — isolation is achieved purely via culling
  masks/layers on the extra camera; shared-space is the default (same
  `Scene`), separate-space requires manually loading an additive scene and
  restricting the camera to it. Confirms: **"which world does the nested
  camera/viewport see" and "what surface does it render to" are orthogonal
  knobs**, and engines that don't reify "world" as a first-class object (Unity)
  end up simulating isolation with layer masks, which is weaker/leaky compared
  to Godot's first-class `World3D`/`World2D` object with a real ownership flag.
- **Nested scenes/prefabs/instancing**: both engines let a scene reference
  another scene/prefab as a subtree (composition, not inheritance) — this is
  just the ordinary scene graph, but it's worth noting it's a *different*
  nesting axis than SubViewport/RenderTexture: prefab-instancing nests
  *geometry* in the *same* render pass; SubViewport/RenderTexture nests a
  *whole separate render pass* whose output becomes an input (texture) to
  another pass. Our design needs both axes too (a GUI panel embedding another
  GUI panel's *widget tree* directly vs. embedding it as an *opaque rendered
  surface*).

## Core design decisions extracted (cross-system pattern)

| Axis | Options seen | Who decides |
|---|---|---|
| **Draws into parent's command stream vs. own surface** | DOM-nested same-process (draws inline) vs. OOPIF/BrowserView/SubViewport/RenderTexture/FBO (separate surface, composited) | Framework, based on isolation need |
| **Composition point** | Immediate-mode inline (cheap, no isolation) vs. retained layer/surface tree resolved by a dedicated compositor (viz aggregator, Wayland compositor, Flutter engine, Godot renderer) | Framework |
| **Damage/redraw scheduling** | Always-sync-with-parent (Wayland sync mode, Godot `WhenVisible`) vs. independent free-running (Wayland desync, Godot `Always`, video overlays) | Per-instance flag |
| **Script/logic space** | Fully shared (same world/agent cluster/JS realm) vs. fully separate (own `World3D`, own browsing context + origin, own process) | Per-instance flag, **this is our "space" switch** |
| **Input routing** | OS/compositor hit-tests the aggregated tree and delivers to the deepest owner in local coords (Chromium viz, Wayland, Flutter TLHC) vs. manual focus-proxy interception + re-dispatch (XEmbed) | Framework; proxy-forwarding is a fallback for platforms without native nested-surface input delivery |
| **Lifecycle independence** | Child can crash/hang/be revised without corrupting the parent's last-good frame (`SurfaceId` versioning) — valuable, should be a target property not just accidental |

## Recommendations for Simple

Adopt three coordinated primitives, one per layer, connected by a single
shared concept — a **RenderSurface** — so all three "nesting" features (2D
offscreen, iframe-in-web, panel-in-panel) are the same mechanism at different
scopes:

1. **2D-renderer layer: `RenderSurface` primitive.**
   A `RenderSurface` = an owned CPU-bitmap-or-Metal-texture render target +
   its own damage/dirty-rect tracker + an update mode (`Always | Once |
   WhenVisible | Never`, Godot-style). Any renderer (2D scene, web engine
   instance, 3D scene) can be told "render into this `RenderSurface`" instead
   of the default target. A `RenderSurface` can itself be sampled as a
   texture by another renderer (2D quad, 3D mesh, or handed to the
   compositor) — this gives feature (1) and is the shared foundation for
   (2)-(4).

2. **WM/compositor layer: surface tree with sync/desync + hit-test.**
   The window manager keeps a retained tree of `RenderSurface`s (mirroring
   Wayland subsurfaces / viz's surface aggregation), each with: parent-relative
   transform/clip, a sync flag (commit atomically with parent vs. free-running),
   and a generation/version id so a hung child keeps showing its last good
   frame rather than corrupting the parent (viz `SurfaceId` lesson). The
   compositor — not individual renderers — performs hit-testing over this
   tree and routes input events to the deepest owning surface in that
   surface's local coordinates; no XEmbed-style manual focus-proxy is needed
   since we control the whole stack, but keep the *concept* (a single
   input-focus owner at the root, explicit focus-in/out notifications to
   nested surfaces) since GUI-panel-embeds-GUI-panel needs focus-ring/IME
   handoff semantics regardless of process boundaries. This gives feature (3),
   and the same tree hosts feature (2)'s per-iframe surface and feature (4)'s
   per-sub-scene surface, so "panel embeds a web panel" and "panel embeds
   another panel" are the same code path with a different renderer plugged
   into the `RenderSurface`.

3. **Web layer: `<iframe>`-equivalent element owning a child renderer
   instance + a "space" descriptor.**
   Each iframe element instantiates its own web-engine instance (own
   DOM/CSSOM/JS realm/layout tree) rendering into a `RenderSurface` (from #1),
   embedded via the surface tree (from #2) at the iframe's layout box. Expose
   exactly one switch, mirroring Godot's `own_world` and the platform's
   agent-cluster/origin distinction, but collapsed into a single flag since we
   don't need Chromium's full generality:
   - **`space: separate` (default)** — new, independent JS realm/global,
     independent DOM, independent storage/cookies-equivalent namespace, no
     synchronous reference back to the host (matches cross-origin iframe +
     separate agent cluster + Godot `own_world=true`). Safe default; matches
     "isolated by default" ask.
   - **`space: shared`** — child explicitly attaches to the parent's realm/DOM
     namespace (matches same-agent-cluster same-origin iframe, or Godot
     `own_world=false`/shared `World2D`) — used for trusted same-app
     compositions (e.g. a design-system "shadow-DOM-like" widget) where the
     host and embedded content are allowed to reach into each other
     synchronously.
   Keep process/thread placement (in-process vs. separate OS thread/process)
   as an orthogonal *deployment* decision from `space` — exactly the lesson
   from Chromium (site isolation process boundary vs. agent-cluster/origin
   script boundary are independent axes) — so `space:separate` doesn't force
   an expensive process spawn unless the embedder also asks for process
   isolation (e.g. `isolation: process` for untrusted third-party content).

4. **3D scene-in-scene (stretch)**: reuse #1/#2 verbatim — a 3D `SubViewport`-
   analogue is just a `RenderSurface` whose renderer is a 3D scene instead of
   2D/web, with the same `space` flag choosing between "render the same
   world from a second camera" (shared) and "render a fully separate
   world" (separate, own scene graph instance).

### Decision table: separate vs. shared space

| Requirement | `space: separate` (default) | `space: shared` |
|---|---|---|
| JS/script realm | New global, no sync access to host | Same realm or explicit bridged access |
| DOM/scene graph | Independent tree | Can be attached into host's tree (Unity RenderTexture "same Scene" analogue) |
| World/physics (3D) | Own `World3D`-equivalent (Godot `own_world=true`) | Shares host's world (camera-in-same-world, e.g. minimap/security-cam) |
| Storage/cookies-equivalent | Isolated namespace | Shared namespace |
| Crash/hang blast radius | Contained; host keeps last-good frame (viz `SurfaceId` versioning) | Same containment via #2's surface-tree versioning regardless of space |
| Use cases | 3rd-party/untrusted web content, ads-equivalent, plugin panels, portrait renderer with independent lighting | Trusted same-app micro-frontends, minimap/security-camera-style views, design-system nested widgets |
| Process/thread placement | Independent axis — choose per trust level, not implied by `space` | Same |

Key citations: Chromium OOPIF rendering design doc and viz Surfaces doc;
Chromium process model & site isolation doc; WICG Origin-Agent-Cluster
explainer; Wayland `wl_subsurface` spec (wayland-book.com); XEmbed protocol
spec (freedesktop.org); Flutter platform-views / Texture-Layer-Hybrid-
Composition docs (flutter/flutter repo); Qt `QQuickRenderControl` docs and
QtWebEngine rendering wiki; Godot `SubViewport` class docs and viewport
tutorial; Electron `BrowserView`→`WebContentsView` migration blog and
`<webview>` tag docs.
