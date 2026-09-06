# `?.` chain on a successful optional collapses to None (interpreter)

Status: OPEN. Filed 2026-08-18 (found during layout_schema.spl SDN reader work).

## Symptom

`get_path(path)?.as_array()`-style optional chaining on an `SdnValue` returns
`None` even when `get_path(path)` itself returns a present value (verified by
splitting into an explicit nested `match`, which works on the same input).
Reproduced in isolation with a minimal script by the agent that hit it.

## Workaround (in tree)

`src/lib/common/spec/evidence/format/layout_schema.spl` — `layout_from_sdn` /
`field_from_sdn` use explicit nested `match` via `sdn_field_text` /
`sdn_field_int` helpers (same style as `cli_extension_config.spl`, which
presumably avoided `?.` for the same reason — an instance of a workaround
being silently normalized, which this doc de-normalizes).

## Wanted (fix test standard applies)

Fix plus: reproduce spec (the exact `expr?.method()` shape on an optional
method result), and similar-case tests: `?.` on a field access, chained
`a?.b()?.c()`, `?.` feeding `??`, and the same shapes on user-defined
optional-returning methods, in both interpreter and codegen lanes.
