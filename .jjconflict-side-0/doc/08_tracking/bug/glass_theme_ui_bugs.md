# Glass Theme + Gemini API — Bug Tracking

## Fixed Bugs (14 total)

### Rendering Pipeline (html.spl)

| ID | Severity | Issue | Fix |
|----|----------|-------|-----|
| GLASS-001 | CRITICAL | `generate_glass_css()` never called — no glass overrides | Added import + append in `html.spl` |
| GLASS-002 | CRITICAL | Glass themes got Catppuccin colors (only checked `== "dark"`) | Added `glass_dark`/`glass_light` color branches |
| GLASS-003 | HIGH | Body font-size 14px instead of glass 15px | Added body override in `glass_component_css()` |

### Token Consistency

| ID | Severity | Issue | Fix |
|----|----------|-------|-----|
| GLASS-004 | HIGH | Dark border `rgba(255,255,255,0.1)` should be `0.08` per tokens | Fixed in `glass_theme.spl` and `html.spl` |
| GLASS-005 | HIGH | Dark surface_bg used `surface_primary` instead of `surface_secondary` | Fixed to `rgba(40,40,48,0.52)` in `html.spl` |

### Backend Support

| ID | Severity | Issue | Fix |
|----|----------|-------|-----|
| GLASS-006 | HIGH | `ui.render/colors.spl` dark detection missed glass/iOS themes | Fixed `get_theme_color()` to check light variants |
| GLASS-007 | HIGH | `ui.render/config.spl` env override only triggered on `"dark"` | Extended to also check `"glass_dark"` |
| GLASS-008 | MEDIUM | `backend_factory.spl` hardcoded `"dark"` default | Changed to `"glass_dark"` |
| GLASS-009 | MEDIUM | ANSI dark detection missed glass/iOS themes | Extended in `style.spl` `AnsiTheme.from_theme()` |

### Glass CSS Widget Coverage

| ID | Severity | Issue | Fix |
|----|----------|-------|-----|
| GLASS-010 | HIGH | 17 widget types missing glass overrides | Added: heading, table, tree, image, scroll, menu sub-elements, dialog/status sub-elements, disabled/readonly/error states, focus ring, tab items |
| GLASS-011 | MEDIUM | CSS class name mismatches (`.widget-text-field` vs `.widget-textfield`) | Added both selectors |
| GLASS-012 | LOW | `.widget-list .list-item:hover` referenced `--ui-hover-bg` | Changed to `--glass-surface-tertiary` |

### Browser Engine (Software Renderer)

| ID | Severity | Issue | Fix |
|----|----------|-------|-----|
| GLASS-013 | CRITICAL | `rgba()` color parsing missing — glass surfaces rendered as black | Added `parse_rgba_func()` and `parse_rgb_func()` in `dom.spl` |
| GLASS-014 | HIGH | No alpha blending in rect fill — translucent surfaces fully opaque | Added alpha check + `put_pixel_blend` in `executor.spl` |
| GLASS-015 | HIGH | Opacity field ignored in paint commands | Added `apply_opacity_to_argb()` in `paint.spl` |
| GLASS-016 | HIGH | `border_radius` ignored — rounded glass panels rendered square | Added `scene_rounded_rect` path in `paint.spl` |
| GLASS-017 | HIGH | CSS `var()` references returned opaque black | Changed to return transparent in `dom.spl` |
| GLASS-018 | MEDIUM | `#RRGGBBAA` 8-char hex colors not parsed | Added 8-char hex support in `dom.spl` |

### Gemini API

| ID | Severity | Issue | Fix |
|----|----------|-------|-----|
| GEMINI-001 | CRITICAL | `_dispatch_gemini_api()` passed standard-format messages without converting to Gemini format | Added `_convert_standard_to_gemini()` in `provider.spl` |
| GEMINI-002 | MEDIUM | Error check after content extraction | Reordered to check errors first |

## Known Limitations

| ID | Severity | Detail |
|----|----------|--------|
| LIM-GLASS-001 | LOW | Software renderer has no `backdrop-filter: blur()` — glass surfaces show translucent but without frosted blur |
| LIM-GLASS-002 | LOW | Gradient rects don't alpha-blend in software renderer (glass doesn't use gradients) |
| LIM-GLASS-003 | LOW | Focus ring glow uses `rgba(10,132,255,0.2)` (dark accent) even in light theme — minor cosmetic |

## Files Modified

### Glass Theme
- `src/lib/common/ui/glass_css.spl` — Full widget coverage (316→596 lines)
- `src/lib/common/ui/glass_theme.spl` — Border color consistency fix
- `src/app/ui.web/html.spl` — Glass CSS integration, color branches

### Backends
- `src/app/ui.render/colors.spl` — Dark theme detection
- `src/app/ui.render/config.spl` — Env var override scope
- `src/lib/common/ui/backend_factory.spl` — Default theme
- `src/lib/common/ui/style.spl` — ANSI dark detection

### Browser Engine
- `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` — rgba(), var(), #RRGGBBAA parsing
- `src/lib/gc_async_mut/gpu/browser_engine/paint.spl` — Opacity, border-radius
- `src/lib/common/render_scene/executor.spl` — Alpha blending

### Gemini API
- `src/lib/nogc_async_mut/llm/provider.spl` — Message format conversion
