# Hair Changer — Requirements

**Feature:** AI-powered virtual hair style try-on web application
**Repository:** Separate private repo (not a submodule of simple)
**Location:** `examples/hair_changer/` (development prototype in simple repo)

## Motivation

Users want to preview how different hairstyles would look on them before visiting a salon. By uploading a selfie and selecting a hair reference image (or choosing from a gallery), the app generates a realistic preview using Gemini 2.5 Flash Image's multi-image composition capabilities.

## Scope

### In Scope
- Web UI with beautiful, modern design
- Multi-language support (Korean primary, English, Japanese)
- Upload face photo + hair reference photo
- Hair option checkboxes: length, type, color/dye, treatment, bangs
- "Enough hair" feasibility indicator based on current vs target length
- Gemini 2.5 Flash Image API for hair transfer generation
- Before/after comparison view
- Style preset gallery with curated hairstyles
- Mobile-responsive layout
- Simple language backend (CLI + HTTP server)

### Out of Scope
- User accounts / login
- Payment processing
- Salon booking integration
- Real-time video/AR try-on
- Model fine-tuning or training

## I/O Examples

### Example 1: Basic Hair Transfer
- **Input:** Face photo (selfie.jpg) + Hair reference (bob_cut.jpg)
- **Options:** Target length=short, Type=straight, Color=natural
- **Output:** Generated image showing user with bob cut hairstyle

### Example 2: Color Change with Style
- **Input:** Face photo + Hair reference (platinum_waves.jpg)
- **Options:** Current length=long, Target=long, Type=wavy, Color=platinum blonde, Dye=yes
- **Output:** Generated image with platinum wavy hair

### Example 3: Korean-style Bangs
- **Input:** Face photo + Gallery preset "Korean curtain bangs"
- **Options:** Current length=medium, Bangs=curtain, Color=dark brown
- **Prompt (Korean UI):** "커튼뱅 스타일로 변환해주세요"
- **Output:** Generated image with Korean-style curtain bangs

### Example 4: Feasibility Warning
- **Input:** Face photo (current: shaved)
- **Options:** Target length=long, Type=curly
- **Output:** Warning: "현재 머리 길이로는 이 스타일이 어렵습니다. 가발이나 익스텐션을 고려해보세요." / "This style may not be achievable with current hair length. Consider extensions."

### Example 5: Gallery Browse (Korean)
- **Input:** User browses gallery in Korean
- **UI:** Category tabs: 숏컷 | 미디엄 | 롱 | 염색 | 펌
- **Output:** Grid of preset styles with Korean names and descriptions

## Acceptance Criteria

- [ ] AC-1: Web UI loads and displays in Korean by default, switchable to EN/JP
- [ ] AC-2: User can upload face photo and hair reference photo
- [ ] AC-3: Hair option checkboxes affect the generation prompt
- [ ] AC-4: Gemini 2.5 API generates hair-transferred image from 2 inputs
- [ ] AC-5: Before/after comparison slider works
- [ ] AC-6: Style gallery shows 10+ preset hairstyles with Korean labels
- [ ] AC-7: Feasibility warning shows when current length < target length threshold
- [ ] AC-8: Mobile-responsive layout works on 375px+ screens
- [ ] AC-9: All UI strings are i18n'd with Korean, English, Japanese
- [ ] AC-10: Result image can be downloaded

## Dependencies

- Gemini 2.5 Flash Image API (via `gemini` CLI or HTTP)
- Simple language HTTP server capabilities (`rt_http_request`, `rt_file_read_text`)
- Web frontend (HTML/CSS/JS served by Simple backend)

## Technical Constraints

- Backend in Simple language (.spl)
- Frontend in HTML/CSS/JS (served as static files by Simple HTTP server)
- Gemini API key required (configured in config.sdn)
- Image uploads stored temporarily in `.build/hair_changer/uploads/`
- Generated results in `.build/hair_changer/results/`

## Language Support

| Language | Code | Priority |
|----------|------|----------|
| Korean | ko | Primary |
| English | en | Secondary |
| Japanese | ja | Tertiary |

### Korean UI Terms

| English | Korean | Context |
|---------|--------|---------|
| Hair Changer | 헤어 체인저 | App title |
| Upload Photo | 사진 업로드 | Button |
| Hair Reference | 헤어 레퍼런스 | Section |
| Generate | 변환하기 | Button |
| Before/After | 변환 전/후 | Comparison |
| Short | 숏 | Length |
| Medium | 미디엄 | Length |
| Long | 롱 | Length |
| Straight | 생머리 | Type |
| Wavy | 웨이브 | Type |
| Curly | 곱슬 | Type |
| Natural | 자연색 | Color |
| Dye | 염색 | Treatment |
| Highlights | 하이라이트 | Treatment |
| Bangs | 앞머리 | Style |
| Curtain Bangs | 커튼뱅 | Style |
| Perm | 펌 | Treatment |
| Download | 다운로드 | Button |
| Style Gallery | 스타일 갤러리 | Section |
| Warning | 주의 | Alert |
