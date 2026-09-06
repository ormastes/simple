<!-- codex-design -->
# Web Renderer Vulkan 4K Showcase — GUI Design

The 4K surface uses a persistent tab strip above one viewport-sized panel. Tabs are `Overview`, `HTML`, `CSS Layout`, `CSS Paint`, `Forms & Media`, `Animation`, and `Evidence`; only one panel is painted at a time so startup and switching stay bounded.

Each feature card displays status (`Renderable`, `Partial`, `Nonpaint`, `Unsupported`) and its minimal visual sample. Production owner and evidence ID belong in optional inspection details or the Evidence panel. Unsupported rows are visible but never styled as passing. Long catalogs use explicit scrolling or pages within the selected panel; all regions needed to see every sample must participate in completeness and pixel evidence.

Keyboard: Left/Right moves tab focus, Home/End jumps, Enter/Space activates, and Tab enters/leaves the strip. Pointer activation uses the same state transition. Selected/focused state is visually distinct and exposed with `tablist`, `tab`, `tabpanel`, `aria-selected`, `aria-controls`, and roving `tabindex`.

The Evidence tab shows requested/resolved backend, adapter/driver, viewport, first-frame/warm timings, fallback, frame digest, Chrome row, and comparison result. Missing evidence stays red/blocked.

Astra review (2026-09-05): this is the intended native UI contract. Browser JavaScript behavior and the standalone pure reducer do not establish native Simple interaction. The current global injected name inventory must become per-panel demonstrations with retained content, and native keyboard/pointer events must reach the shared state owner before this design is considered implemented.
