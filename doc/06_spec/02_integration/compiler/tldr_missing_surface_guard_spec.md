# TLDR missing ordinary source surface guard

Executable: `test/02_integration/compiler/tldr_missing_surface_guard_spec.spl`.
All five criteria are **UNRUN**; native product qualification is pending.

| Requirement | Real operation | Required result |
|---|---|---|
| REQ-TLDR-FALLBACK-001 | Parse mixed Record/add fixture; authenticate function header; run actual import resolver without provider surface | One explicit missing ordinary-route diagnostic, no partial add binding |
| REQ-TLDR-FALLBACK-002 | Parse namespace fixture and invoke actual resolver | Explicit diagnostic instead of silently dropping namespace |
| REQ-TLDR-FALLBACK-003 | Parse generic identity call/import and invoke actual resolver | Explicit body/surface prerequisite diagnostic |
| REQ-TLDR-FALLBACK-004 | Parse provider and mixed consumer; build real canonical surfaces; resolve imports | Both Record and add registered without errors |
| REQ-TLDR-FALLBACK-005 | Parse ordinary add import with authenticated header only | Function registers with admitted ABI without requiring source |

The fixture entrypoints each return42 when compiled through a complete ordinary source closure. Package-index archive-backed native runs must exercise these same consumers: supported function headers remain usable; omitted body/type surfaces must reject before successful output. Those native tests are UNRUN.

These owner tests explicitly supply an authenticated header; the driver still requires strict entry-only opt-in. This is an interim correctness guard, **not default header admission or automatic source fallback**. The package planner still needs a surface/body demand route that accounts for dirty tasks, archive actions and source authority before excluding source. Cached objects are not deleted or reclassified. See `doc/08_tracking/bug/tldr_ordinary_fallback_excluded_source_20261008.md`.
