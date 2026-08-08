# Responsive / Adaptive Layout Across Production Platforms

**Date:** 2026-06-12
**Phase:** 01_research / ui / responsive_layout
**Purpose:** Survey how production platforms restructure layout across phone / tablet / desktop,
how cross-platform GUI stacks handle GPU backends + form-factor adaptation, and derive an
adopted design for Simple (SPipe `mobile-gui-platform`, AC-1).

Existing Simple baseline referenced throughout:
- `src/lib/common/ui/profile.spl` — `SizeClass` Compact/Regular/Expanded, pixel breakpoints 600/1200
  (terminal breakpoints 80/160 columns), `Orientation` Landscape/Portrait/Square.
- Engine2D with Metal + Vulkan backends; Tauri webview backend emitting generated `@media` CSS.

---

## 1. How platforms restructure layout per form factor

### 1.1 Web (CSS)

- **Media queries** (`@media (min-width: ...)`) remain the primary mechanism; **container
  queries** (`@container`) are now broadly supported and let a *component* adapt to its parent's
  size instead of the viewport (https://tailwindcss.com/docs/responsive-design,
  https://blog.logrocket.com/tailwind-css-dynamic-breakpoints-container-queries/).
- **Mobile-first** is the dominant convention: unprefixed styles target the smallest width,
  larger breakpoints layer on via `min-width` (Tailwind, Bootstrap both do this).
- Common breakpoint sets:
  - **Tailwind:** sm 640, md 768, lg 1024, xl 1280, 2xl 1536 px
    (https://tailwindcss.com/docs/responsive-design).
  - **Bootstrap:** sm 576, md 768, lg 992, xl 1200, xxl 1400 px.
  - **Material 3 (web + Android, dp):** compact <600, medium 600–839, expanded 840–1199,
    large 1200–1599, extra-large ≥1600
    (https://m3.material.io/foundations/layout/applying-layout/window-size-classes).
- Takeaway: there is no single canonical pixel set, but **600 and 840** recur as the
  phone→tablet and tablet→desktop-ish boundaries in the Material family, while web frameworks
  cluster around 576–640 / 768 / 992–1024 / 1200–1280.

### 1.2 iOS / iPadOS (UIKit / SwiftUI)

- **Size classes are a two-axis, two-value model:** `horizontalSizeClass` and
  `verticalSizeClass`, each `.compact` or `.regular`
  (https://developer.apple.com/documentation/swiftui/userinterfacesizeclass,
  https://www.hackingwithswift.com/quick-start/swiftui/how-to-create-different-layouts-using-size-classes).
- Canonical mappings: iPhone portrait = compact-w / regular-h; iPhone landscape =
  compact-h (regular-w only on Max/Plus phones); iPad = regular/regular in both orientations —
  but iPad **Split View/Slide Over** (1/3, 1/2, 2/3 widths) can demote an app to compact-w
  (https://github.com/renaudjenny/SwiftUI-with-Size-Classes). So size class is a *window*
  property, not a device property.
- **Navigation restructuring:** `NavigationSplitView` renders a 2–3 column sidebar+detail layout
  when regular-w and automatically collapses to a navigation stack when compact-w
  (https://eon.codes/blog/2024/02/02/NavigationSplitView-in-swiftui/). iPadOS 18+ also morphs
  tab bars into sidebars (`TabView` `.sidebarAdaptable`).
- **Safe areas:** layout must inset for notch / home indicator / rounded corners; safe-area
  insets are per-window values the layout system exposes, orthogonal to size class.
- Apple does not publish dp breakpoints — size class is assigned by the OS per window; apps
  branch only on compact/regular.

### 1.3 Android (Jetpack Compose / Material 3)

- **WindowSizeClass:** width classes compact <600dp, medium 600–839dp, expanded ≥840dp;
  height classes compact <480dp, medium 480–899dp, expanded ≥900dp. Material 3 extends width
  with large 1200–1599dp and extra-large ≥1600dp
  (https://m3.material.io/foundations/layout/applying-layout/window-size-classes,
  https://developer.android.com/codelabs/adaptive-material-guidance).
- **Canonical layouts** (https://developer.android.com/develop/adaptive-apps/guides/canonical-layouts):
  - **List-detail** (`ListDetailPaneScaffold`): one pane on compact, two side-by-side panes on
    expanded; handles back-stack collapse automatically
    (https://developer.android.com/develop/ui/compose/layouts/adaptive/list-detail).
  - **Feed**: grid whose column count grows with width class.
  - **Supporting pane** (`SupportingPaneScaffold`): primary content ~2/3 + supporting pane ~1/3
    on expanded; supporting content moves below/into sheet on compact.
- **Adaptive navigation:** `NavigationSuiteScaffold` swaps top-level navigation automatically:
  **bottom navigation bar** (compact) → **navigation rail** (medium/expanded) → can host a
  **navigation drawer** for large displays
  (https://developer.android.com/develop/ui/compose/layouts/adaptive/build-adaptive-navigation,
  https://android-developers.googleblog.com/2024/09/jetpack-compose-apis-for-building-adaptive-layouts-material-guidance-now-stable.html).
- Guidance explicitly says: branch on window size class, **never on device type or physical
  screen** (https://developer.android.com/develop/ui/compose/layouts/adaptive/adaptive-dos-and-donts) —
  multi-window/foldables make "device type" lie.

### 1.4 Flutter

- **`MediaQuery`** gives viewport size/DPR/padding (viewport-scoped);
  **`LayoutBuilder`** gives parent constraints (container-scoped — Flutter's analog of container
  queries); `OrientationBuilder` for orientation.
- No built-in size-class enum in the core SDK; the **Material 3 adaptive packages**
  (`flutter_adaptive_scaffold`, now superseded by the `material3_adaptive` work) implement the
  Material breakpoints (600/840/...) and the bottom-bar↔rail↔drawer switch; community
  `material_design` package exposes `M3BreakpointToken` with the same numbers
  (https://pub.dev/documentation/material_design/latest/material_design/M3BreakpointToken.html).

### 1.5 Desktop toolkits

- **GTK / libadwaita:** `AdwBreakpoint` — declarative breakpoints attached to a window/dialog
  that set widget properties when the window crosses a size condition; plus adaptive widgets
  (`AdwNavigationSplitView` sidebar↔stack, `AdwViewSwitcher`→`AdwViewSwitcherBar` top↔bottom
  tabs, `AdwMultiLayoutView` for reparenting children between entirely different layouts)
  (https://gnome.pages.gitlab.gnome.org/libadwaita/doc/main/adaptive-layouts.html).
- **WinUI / UWP:** `AdaptiveTrigger` with `MinWindowWidth` drives `VisualStateManager` state
  changes; `NavigationView` auto mode uses **640/641 and 1007/1008 px** thresholds:
  ≤640 minimal (hamburger only), 641–1007 compact rail (icons only), ≥1008 expanded pane
  (https://learn.microsoft.com/en-us/windows/apps/develop/ui/controls/navigationview,
  https://learn.microsoft.com/en-us/uwp/api/windows.ui.xaml.adaptivetrigger).
- **Qt:** no built-in breakpoint system; QML apps branch manually on window width/`Screen`
  properties or use Qt Quick Controls' layout primitives. Qt's strength is the rendering
  abstraction (RHI, §2), not form-factor policy.

---

## 2. Cross-platform GUI stacks: GPU backends, adaptation, one-source

| Platform | (a) GPU drawing backend | (b) Form-factor adaptation | (c) One-source model |
|---|---|---|---|
| **Flutter** | **Impeller**: Metal on iOS/macOS, Vulkan on Android (API 29+) with **OpenGL ES fallback** for non-Vulkan devices; shaders precompiled at build time to Metal IR / SPIR-V (no runtime shader jank). Windows/Linux still Skia-based (https://docs.flutter.dev/perf/impeller) | MediaQuery/LayoutBuilder + Material adaptive packages (600/840) | Single Dart tree, framework draws every pixel |
| **React Native** | Does **not** draw itself — Fabric renderer (new architecture, default since 0.76) creates **native platform views**; GPU work is the OS toolkit's (https://kotlinlang.org/docs/multiplatform/kotlin-multiplatform-react-native.html) | Manual (`useWindowDimensions`) + community libs | Single JS/TS tree, per-platform components common |
| **Compose Multiplatform** | **Skia via Skiko** everywhere off-Android: Metal on iOS, OpenGL/Metal via AWT on desktop, WebGL/Canvas on web (https://deepwiki.com/JetBrains/compose-multiplatform/2.1-core-framework-and-skiko) | `WindowSizeClass` (600/840) + `NavigationSuiteScaffold`, multiplatform port (https://github.com/chrisbanes/material3-windowsizeclass-multiplatform) | Single Kotlin tree |
| **Tauri** | No GPU layer of its own — **system webview**: WKWebView (macOS/iOS), WebView2/Chromium (Windows), WebKitGTK (Linux), Android System WebView (https://v2.tauri.app/reference/webview-versions/) | CSS media/container queries inside the webview | Single HTML/CSS/JS frontend + Rust core |
| **Qt / Qt Quick** | **QRhi** abstraction: D3D11/12 on Windows, **Metal on macOS/iOS, Vulkan/OpenGL elsewhere**; Qt 6 scene graph always goes through RHI (https://www.qt.io/blog/graphics-in-qt-6.0-qrhi-qt-quick-qt-quick-3d) | Manual width branching in QML | Single QML/C++ tree |
| **.NET MAUI** | Native controls via per-platform handlers (no own GPU renderer; optional SkiaSharp canvas) | `OnIdiom` (Phone/Tablet/Desktop) + `AdaptiveTrigger`-style visual states | Single C#/XAML tree |
| **egui** | Immediate-mode; renders via **wgpu** (Metal/Vulkan/D3D12/GL) or glow | None built in — apps branch on available rect | Single Rust tree |
| **Slint** | **Skia renderer** (Metal/Vulkan/D3D/OpenGL) or FemtoVG (GL/wgpu) (https://docs.slint.dev/latest/docs/slint/guide/backends-and-renderers/backends_and_renderers/) | Property-driven; no breakpoint framework | Single `.slint` markup |

Patterns worth noting:
1. The serious "draw-everything" stacks (Flutter, Compose MP, Slint, Qt, egui) all converged on a
   **thin HAL over Metal+Vulkan+D3D with a GL fallback** — exactly the position Simple's Engine2D
   (Metal + Vulkan) is already in.
2. The form-factor layer is **independent of the GPU layer** in every stack — adaptation is a
   pure layout/policy module fed by window metrics.
3. Everyone who has a real adaptive story (Compose, Flutter/Material, libadwaita, WinUI) ships
   **named size classes + a small set of canonical layout scaffolds**, not raw breakpoints in
   app code.

---

## 3. Common adaptive patterns worth adopting

- **Two-axis size classes:** width class drives structure (columns, navigation); height class
  handles landscape-phone degeneracy (Apple compact-h; Material height-compact <480dp).
- **Converged width breakpoints:** 600dp (phone→tablet) and 840dp (tablet→expanded) — shared by
  Material 3, Compose, Flutter adaptive; WinUI's 641/1008 are the same idea shifted for desktop.
- **Adaptive top-level navigation:** bottom bar (compact) → navigation rail (medium) →
  persistent drawer/sidebar (expanded). Identical morphology in Compose
  `NavigationSuiteScaffold`, WinUI `NavigationView` auto mode, libadwaita split view, SwiftUI
  `NavigationSplitView`/sidebar-adaptable tabs.
- **List-detail collapse:** two panes ≥840dp, single pane with push navigation below; the
  scaffold owns the back-stack semantics.
- **Supporting pane:** ~2/3 primary + ~1/3 supporting on expanded; supporting content drops to a
  bottom sheet/below on compact.
- **Touch-target minimums:** 44×44 pt (Apple HIG), 48×48 dp (Material); WCAG 2.2 AA floor is
  24×24 CSS px, AAA 44×44 (https://blog.logrocket.com/ux-design/all-accessible-touch-target-sizes/).
  Pointer-primary (desktop) UIs may use denser controls (~28–32px rows).
- **Density/spacing scaling:** larger classes get wider margins (Material: 16dp compact body
  margin → 24dp medium+), max content widths, and multi-column grids; desktop adds hover states
  and compact density.
- **Window, not device:** every modern system classifies the *window* (split view, foldables,
  desktop resizing), and re-evaluates on resize.

---

## 4. Adopted design for Simple

### 4.1 DeviceClass — phone / tablet / desktop

Add `enum DeviceClass: Phone, Tablet, Desktop` alongside (not replacing) `SizeClass`.
Derivation rule (evaluated once per window creation, re-evaluated only on display change):

```
fn derive_device_class(platform, touch_primary, shortest_side_dp) -> DeviceClass:
    if platform in {macos, windows, linux_desktop} and not touch_primary: return Desktop
    if shortest_side_dp >= 600: return Tablet      # Android/Material tablet rule
    return Phone
```

- `touch_primary` = the platform reports touch as primary pointer (iOS/Android true; desktop
  false unless a touch-only device).
- DeviceClass selects **interaction policy** (touch-target floor 44pt/48dp vs dense pointer
  targets, hover affordances, scrollbar style, default density). It must **never** select
  layout structure — that is SizeClass's job, because split-screen tablets and resized desktop
  windows cross structural boundaries at runtime (per Android do's-and-don'ts guidance).

### 4.2 Breakpoints — align with Material: 600 / 840 (recommended)

Change `default_breakpoints()` from `(compact_max: 600, regular_max: 1200)` to
`(compact_max: 600, regular_max: 840)` in dp (density-independent units, not raw px).

Reasoning:
- 600 already agrees with Material/Compose/Flutter; only the second boundary differs.
- With 1200, an iPad landscape (1024–1194 pt) and the WinUI expanded-pane zone (≥1008 px) land
  in *Regular* and never get sidebar/two-pane layouts — visibly wrong on real tablets.
- 840 lets Simple reuse Material's canonical-layout specs and test fixtures verbatim, and
  matches the multiplatform ecosystem (Compose MP, Flutter adaptive, SAP Fiori Android).
- Keep `Expanded` open-ended for now; if desktop-specific tuning is needed later, add a fourth
  `Large` class at 1200 (Material large) rather than moving 840.
- Tauri/web backend: generated `@media` CSS emits `min-width: 600px` / `min-width: 840px`,
  mobile-first ordering. Terminal breakpoints (80/160 cols) are unaffected.

### 4.3 Two-axis size classes

Extend the profile to `width_class` + `height_class` (both `SizeClass`), Apple/Material style:
- Width thresholds: 600 / 840 dp (above). Height thresholds: 480 / 900 dp (Material height
  classes). `Orientation` stays as a derived convenience.
- Width class drives structure (panes, navigation); height class compact triggers
  landscape-phone behaviors (collapse top bars, suppress bottom navigation in favor of rail).

### 4.4 Adaptive patterns to implement first (priority order)

1. **AdaptiveNavScaffold** — bottom bar (width compact) → nav rail (regular/medium) →
   persistent sidebar/drawer (expanded); the single highest-leverage pattern, mirrored by
   Compose/WinUI/libadwaita/SwiftUI. Use rail instead of bottom bar when height is compact.
2. **ListDetailScaffold** — two panes ≥840dp, single pane + push/back below; scaffold owns the
   collapse and back semantics.
3. **Touch-target + density policy from DeviceClass** — min hit size 44pt (Phone/Tablet on
   Apple), 48dp (Phone/Tablet elsewhere), dense (~32px) on Desktop; spacing token set per
   width class (16dp margins compact → 24dp regular+).
4. **SupportingPaneScaffold** (2/3 + 1/3, sheet on compact) — after 1–3 prove the scaffold
   plumbing.
- Defer: container queries (component-scoped classes à la `LayoutBuilder`/`@container`) — the
  scaffolds cover the near-term need; revisit when nested adaptive components appear.

### 4.5 Non-goals confirmed by survey

- No per-device hardcoding (model lists, "isTablet" from screen hardware).
- No new GPU work required: Engine2D Metal+Vulkan already matches the Flutter/Qt/Slint backend
  shape; the adaptive layer is pure `common/ui` policy fed by viewport metrics from any backend
  (Engine2D window, Tauri webview, terminal).
