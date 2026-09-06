<!-- codex-design -->
# Simple Web Browser Production GUI

## Primary window

```text
┌──────────────────────────────────────────────────────────────────────────┐
│ ←  →  ■  ↻  ⌂  ☆ │ https://example.test/page                    [Go] │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  Rendered page content                                                   │
│                                                                          │
│  Name  [Ada Lovelace________________]  [Submit]                           │
│                                                                          │
│  Animated status: ●                                                      │
│                                                                          │
├──────────────────────────────────────────────────────────────────────────┤
│ Secure · example.test · Loading… / Ready / Error                          │
└──────────────────────────────────────────────────────────────────────────┘
```

Controls keep canonical IDs `back`, `forward`, `stop`, `home`, `favorite`,
`address`, and `title`; add `reload`. “Favorite” may display as Bookmark while
retaining the stable ID.

## Interaction rules

- Address `set_value` edits a draft; Enter/Go submits it.
- Back/forward enable from history position.
- Stop enables only while work is pending and prevents late commit.
- Reload does not add a history entry.
- Bookmark toggles add/remove and reflects selected state.
- Page controls expose stable DOM-node semantic IDs, focus, value, enabled,
  selected, role, name, and actions.
- Keyboard focus is always visible.
- Network/TLS/security errors preserve the last committed page and show a
  non-secret typed status.

## Evidence

Structured UI access and Draw IR are primary. Screenshots under
`doc/06_spec/image/03_system/app/browser/feature/simple_web_browser_engine_production_hardening/`
are supplemental.
