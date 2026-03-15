# Hair Changer — Plan

**Requirement:** doc/requirement/hair_changer.md
**Research:** doc/research/hair_changer.md
**Design:** doc/design/hair_changer.md

## Objective

Build a beautiful, Korean-first web application for virtual hair style try-on using Gemini 2.5 Flash Image. Users upload a face photo and hair reference, select options, and receive a realistic hair-transferred preview.

## Current Status

| Component | Status | Evidence |
|-----------|--------|----------|
| HTTP Server FFI | Real | src/lib/nogc_sync_mut/io/http_ffi.spl |
| Gemini CLI Provider | Real | examples/simple_aidev/transform/provider/gemini.spl |
| Web Dashboard | Real | src/app/web_dashboard/server.spl |
| Hair Changer App | New | Not yet created |

## What To Do

1. **Create project structure** (difficulty: 1)
   - MDSOC directories: entity/, feature/, transform/, shared/
   - Static web files: web/
   - Config: config.sdn
   - Gallery presets: gallery/

2. **Implement i18n system** (difficulty: 2)
   - JSON translation files: web/i18n/ko.json, en.json, ja.json
   - JavaScript i18n loader with fallback chain
   - All UI strings externalized

3. **Build web frontend** (difficulty: 3)
   - Modern Korean aesthetic (clean, minimal, soft gradients)
   - Responsive layout (mobile-first, 375px+)
   - Photo upload with drag-and-drop
   - Hair options panel with checkboxes
   - Before/after comparison slider
   - Style gallery grid
   - Language switcher (KO/EN/JA)

4. **Implement backend HTTP server** (difficulty: 2)
   - Static file serving for web/
   - POST /api/upload — receive images
   - POST /api/generate — call Gemini, return result
   - GET /api/gallery — list presets
   - GET /api/health — health check

5. **Implement Gemini image transform** (difficulty: 3)
   - Build prompt from hair options
   - Call gemini CLI with face + hair reference images
   - Parse response, extract generated image
   - Save result to .build/hair_changer/results/

6. **Create style gallery presets** (difficulty: 1)
   - 12+ preset styles with Korean/English/Japanese names
   - Categories: short, medium, long, dyed, permed
   - Thumbnail images for each preset

7. **Implement feasibility checker** (difficulty: 2)
   - Current length vs target length comparison
   - Warning messages in all 3 languages
   - Suggest alternatives when not feasible

8. **Testing and polish** (difficulty: 2)
   - Spec tests for backend API
   - Visual polish, animations
   - Error handling for API failures

## Dependencies

```
Task 1 → Task 2, 3, 4 (parallel after structure)
Task 2 → Task 3 (i18n needed for UI)
Task 4 → Task 5 (server needed for Gemini calls)
Task 3 + 5 → Task 6 (gallery needs UI + backend)
Task 3 → Task 7 (feasibility needs UI)
All → Task 8
```
