# Web Renderer Vulkan 4K Showcase Hardening — Feature Requirements

- REQ-WEB4K-001: A production-adjacent typed inventory classifies every known HTML tag and implemented CSS property/value family as `renderable`, `partial`, `nonpaint`, or `unsupported`, with production owner, test, and showcase-tab traceability.
- REQ-WEB4K-002: The canonical web showcase covers every `renderable` row and visibly labels partial, nonpaint, and unsupported rows without claiming pixels for them.
- REQ-WEB4K-003: The showcase exposes stable accessible tabs selectable by pointer and keyboard, including Arrow/Home/End focus movement and Enter/Space activation.
- REQ-WEB4K-004: The canonical installed runner supports a 3840×2160 Vulkan request and fails closed if the requested backend is not a real admitted Vulkan device.
- REQ-WEB4K-005: A source-bound receipt measures process start through first complete present, warm redraw, tab switch, frame identity, backend identity, fallback, dropped work, and max RSS.
- REQ-WEB4K-006: A real Chrome module runs the identical versioned fixture and produces comparable per-tab timing, backend, image, and RSS evidence.
- REQ-WEB4K-007: All-tab pairwise comparison fails on missing/stale captures, mismatched viewport/scale, backend failure, or documented pixel threshold violation.
- REQ-WEB4K-008: Changes preserve BrowserSession → HTML/CSS → Draw IR → Engine2D → Vulkan ownership, public behavior, deterministic pixels, fallback semantics, and the one-app/host-interface rule.

