<!-- codex-design -->
# Detail Design: WM Glass Theme on Host and SimpleOS

## Data Model

Add common value types in `common.ui.theme_render_snapshot`:

- `ThemeShadowLayer`: x/y offset, blur, spread, RGBA and inset.
- `ThemeMaterialSemantics`: desktop, window, active/inactive title surfaces;
  alpha, blur, saturation, border width/RGBA, radius, ordered shadows,
  typography/text, reduced-transparency solid fallback and contrast.
- `ThemeRenderSnapshot`: ID, family, source reference, source-manifest SHA-256,
  normalized-material SHA-256, composed CSS, semantic colors and material.

The snapshot is immutable by convention. `ResolvedThemePackage` constructs it;
the generated bare-metal module returns the same value. Normalization uses a
fixed field order and integer units (`RGBA8`, pixels, alpha/saturation/contrast
in thousandths) before hashing.

## Theme Package Changes

1. Parse RGBA rather than falling back to opaque hard-coded colors.
2. Parse shape radius/blur/elevation and base typography/material variables.
3. Preserve ordered layered shadows and active/inactive variants.
4. Define/validate missing package variables required by the material contract.
5. Replace `path:length` fingerprinting with sorted path/content SHA-256.
6. Cache by canonical ID and source manifest; expose explicit invalidation only.

## Startup Adapters

`install_resolved_wm_theme(snapshot)` maps the full snapshot into existing WM
theme state. Hosted bootstrap calls it before creating `HostCompositor`.
`gui_entry_desktop.spl` installs `generated_aetheric_dark_theme_snapshot()`
before `DesktopShell` renders its first frame. Both emit the same normalized
identity record.

`WmChromeColors` remains source compatible but gains or composes a material
record; every production consumer reads the installed theme. Default Aqua
values are used only if installation fails and that state is reported as an
unaccepted emergency fallback.

## Web and CSS Changes

`simple_web_content_render_request_with_theme` receives a cached snapshot (or
its CSS/fingerprint) rather than branching on theme-name strings. Request and
content-cache revisions include the material hash. Structural WM layout CSS is
appended after package CSS but contains no visual palette.

The production Style/computed-style model gains ordered shadow layers and
backdrop blur/saturation. Draw IR style projection preserves the same values.
The older DOM accessor layer must return stored semantics rather than constant
zeros/empty arrays so `layout_paint` is internally coherent. Existing feature
gap tests change backdrop blur from known-unsupported to supported or explicit
capability fallback.

## Rendering Algorithm

For each glass box: paint prior background; render ordered outer shadows;
sample/blur/saturate the bounded backdrop when available; composite translucent
surface; paint inset shadows, border, then content/text. When unavailable or
reduced transparency is requested, paint the declared solid fallback and emit
realized capability state. Never silently substitute opaque default colors.

## Evidence Model

`wm-glass-theme-evidence-v1` separates requested semantics from realized
capabilities. Per blur/shadow/gradient/font/GPU/readback capability record:
requested, `available|unavailable`, proof rung, implementation, fallback used,
fallback kind/reason and realized hash. `unknown` is invalid.

GPU proof order is BAR2 mapped, hello acknowledged, backend selected, Draw IR
submission accepted, device receipt valid, readback presented, independent QMP
`pmemsave`. Record highest passed and first unavailable.

## Error Handling

Invalid package/schema/hash/snapshot drift fails before theme installation.
Unknown capability, compatibility renderer, legacy entry, stale revision,
wrong-process capture or mismatched hash rejects evidence. Runtime inability to
blur uses the named solid fallback and remains operational but cannot masquerade
as native blur.

## Performance

Measure cached warm host startup, frame p50/p95/max, input-to-present, QEMU
launch-to-first-themed-frame, QEMU themed-frame latency and max RSS. Package
parsing/generation is outside hot paths; frame rendering performs no file scan,
CSS package load or subprocess.
