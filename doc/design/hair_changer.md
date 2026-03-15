# Hair Changer — Design

**Requirement:** doc/requirement/hair_changer.md
**Plan:** doc/plan/hair_changer.md

## MDSOC Architecture

```
examples/hair_changer/
  main.spl                          # Entry point: HTTP server + CLI
  config.sdn                        # Gemini API config

  entity/
    hair_options.spl                # HairOptions struct (length, type, color, etc.)
    generation_request.spl          # GenerationRequest struct
    style_preset.spl                # StylePreset struct

  feature/
    server/routes.spl               # HTTP route handlers
    server/static.spl               # Static file serving config
    gallery/presets.spl             # Load and list gallery presets
    gallery/categories.spl          # Category definitions
    feasibility/checker.spl         # Hair length feasibility logic

  transform/
    gemini/prompt_builder.spl       # Build Gemini prompt from options
    gemini/image_handler.spl        # Call Gemini API, handle response

  shared/
    config_loader.spl               # SDN config parser
    file_utils.spl                  # Image file I/O utilities

  web/                              # Static frontend (HTML/CSS/JS)
    index.html                      # Main SPA page
    css/
      style.css                     # Main styles (Korean aesthetic)
      slider.css                    # Before/after slider
      gallery.css                   # Gallery grid
      responsive.css                # Mobile breakpoints
    js/
      app.js                        # Main app logic
      i18n.js                       # Internationalization
      upload.js                     # Image upload handling
      options.js                    # Hair options panel
      slider.js                     # Before/after comparison
      gallery.js                    # Style gallery
      api.js                        # Backend API calls
    i18n/
      ko.json                       # Korean translations
      en.json                       # English translations
      ja.json                       # Japanese translations
    img/
      logo.svg                      # App logo
      gallery/                      # Preset thumbnails

  gallery/                          # Preset definitions (SDN)
    short_bob.sdn
    korean_bangs.sdn
    long_waves.sdn
    pixie_cut.sdn
    layered_medium.sdn
    curtain_bangs.sdn
    platinum_blonde.sdn
    ash_brown.sdn
    red_highlights.sdn
    natural_perm.sdn
    digital_perm.sdn
    two_block.sdn

  test/
    routes_spec.spl                 # API route tests
    prompt_builder_spec.spl         # Prompt generation tests
    feasibility_spec.spl            # Feasibility checker tests
```

## Type Definitions

### HairOptions
```simple
struct HairOptions:
    current_length: text       # "shaved", "short", "medium", "long"
    target_length: text        # "short", "medium", "long"
    hair_type: text            # "straight", "wavy", "curly", "coily"
    color: text                # "natural", "blonde", "brunette", "red", etc.
    dye: bool                  # Whether to apply color
    treatment: text            # "none", "highlights", "balayage", "ombre"
    bangs: text                # "none", "side", "curtain", "blunt"
    volume: text               # "thin", "normal", "thick"
    perm: bool                 # Whether perm style
```

### GenerationRequest
```simple
struct GenerationRequest:
    face_image_path: text
    hair_ref_path: text
    options: text              # serialized options
    output_path: text
    lang: text                 # "ko", "en", "ja"
```

### StylePreset
```simple
struct StylePreset:
    id: text
    name_ko: text
    name_en: text
    name_ja: text
    category: text             # "short", "medium", "long", "color", "perm"
    thumbnail: text            # path to thumbnail image
    options: text              # default options for this preset
```

## API Surface

| Method | Path | Description |
|--------|------|-------------|
| GET | / | Serve index.html |
| GET | /css/* | Static CSS files |
| GET | /js/* | Static JS files |
| GET | /i18n/* | Translation JSON files |
| GET | /img/* | Image assets |
| POST | /api/upload | Upload face/hair images, returns paths |
| POST | /api/generate | Generate hair transfer, returns result image |
| GET | /api/gallery | List all style presets |
| GET | /api/gallery/:id | Get preset details |
| GET | /api/health | Health check |

## Visual Design

### Color Palette (Korean Aesthetic)
```
Primary:     #8B5CF6 (soft purple)
Secondary:   #F472B6 (rose pink)
Background:  #FAFAF9 (warm white)
Surface:     #FFFFFF (white cards)
Text:        #1C1917 (near black)
Muted:       #78716C (warm gray)
Success:     #22C55E (green)
Warning:     #F59E0B (amber)
Accent:      linear-gradient(135deg, #8B5CF6, #F472B6)
```

### Layout (Mobile-First)
```
┌──────────────────────────────────────┐
│  헤어 체인저              [KO|EN|JA] │  <- Header with lang switcher
├──────────────────────────────────────┤
│  ┌────────────┐  ┌────────────┐     │
│  │   사진     │  │  레퍼런스   │     │  <- Upload area (drag & drop)
│  │  업로드    │  │   업로드    │     │
│  └────────────┘  └────────────┘     │
├──────────────────────────────────────┤
│  머리 옵션                           │
│  ┌─────────────────────────────┐    │
│  │ 길이: ○숏 ○미디엄 ●롱      │    │  <- Radio buttons
│  │ 타입: ○생머리 ●웨이브 ○곱슬 │    │
│  │ 색상: ○자연색 ○금발 ●갈색  │    │
│  │ ☐ 염색  ☐ 하이라이트  ☐ 펌 │    │  <- Checkboxes
│  │ 앞머리: ○없음 ●커튼뱅 ○풀뱅│    │
│  └─────────────────────────────┘    │
│         [ 변환하기 ]                 │  <- Generate button (gradient)
├──────────────────────────────────────┤
│  변환 전/후                          │
│  ┌──────────┬──────────┐            │
│  │  Before  │  After   │            │  <- Comparison slider
│  │          │          │            │
│  └──────────┴──────────┘            │
│         [ 다운로드 ]                 │
├──────────────────────────────────────┤
│  스타일 갤러리                       │
│  [숏컷] [미디엄] [롱] [염색] [펌]   │  <- Category tabs
│  ┌────┐ ┌────┐ ┌────┐ ┌────┐       │
│  │    │ │    │ │    │ │    │       │
│  │보브│ │커튼│ │웨이│ │투블│       │  <- Preset grid
│  └────┘ └────┘ └────┘ └────┘       │
└──────────────────────────────────────┘
```

### Responsive Breakpoints
- Mobile: 375px — single column, stacked uploads
- Tablet: 768px — side-by-side uploads, wider options
- Desktop: 1024px+ — full layout, gallery 4-column

### Animations
- Upload area: pulse on drag-over, fade-in preview
- Generate button: shimmer gradient animation while processing
- Result: slide-in from bottom with spring easing
- Gallery cards: hover scale 1.05 with shadow lift

### Accessibility
- All interactive elements keyboard-focusable
- ARIA labels in current language
- Color contrast ratio >= 4.5:1
- Reduced motion media query support
