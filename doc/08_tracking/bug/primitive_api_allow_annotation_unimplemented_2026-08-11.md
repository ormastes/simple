## Re-verified 2026-08-17 — STILL OPEN, unchanged

`/usr/bin/grep -rn "allow_attr\|is_allowed\|allow_attribute" src/compiler/35.semantics/lint/*.spl`
returns **zero** lines. No suppression machinery exists; the `@allow(primitive_api)` /
`#[allow(raw_unit)]` headers already in `src/lib/nogc_sync_mut/engine/physics/*.spl`
are still inert. Unchanged from the original filing.

# `@allow(primitive_api)` / `#[allow(raw_unit)]` suppression is documented but never implemented

**Status:** OPEN
**Found:** 2026-08-11, while landing the LLM fraud-prevention rules.sdl work.

## Summary

`src/compiler/35.semantics/lint/primitive_api.spl` documents two suppression
mechanisms in its own header comments:

```
# - Code annotated with @allow(primitive_api)
```
and, for the neighboring `raw_unit` rule:
```
# Suppressible via `#[allow(raw_unit)]` on the call site / enclosing statement
# / function / module (handled by the shared allow-attr machinery).
```

Neither exists. `grep -rn "allow_attr\|is_allowed\|allow_attribute" src/compiler/35.semantics/lint/*.spl`
returns nothing but the doc comments themselves. `check_function`,
`check_module_items`, and `check_call_site` in `primitive_api.spl` have no
attribute lookup of any kind — the only exemption implemented is
`is_pure_math_function` (all params + return share one bare primitive type,
e.g. `fn abs(x: f64) -> f64`). Physics files under
`src/lib/nogc_sync_mut/engine/physics/*.spl` already carry
`@allow(primitive_api)` / `#![allow(primitive_api)]` headers as if this were
load-bearing; it silently does nothing for them today.

## Evidence

- Added `#![allow(primitive_api)]` as the first line of
  `src/lib/common/spec/evidence/model.spl` and re-ran
  `bin/simple lint src/lib/common/spec/evidence/model.spl`: still reports the
  same 16 `error[primitive_api]` findings, byte-identical to a run without the
  annotation.
- `check_module_items(items: [Node])` receives only the module's item list,
  no file-level attribute/annotation context at all — so even a correct fix
  needs new plumbing from the caller (`semantic_api/checker.spl`) to carry
  file-level `#![allow(...)]` state down to the rule, not just a local check.

## Secondary finding: pre-existing primitive_api debt in model.spl

Independent of the above, `src/lib/common/spec/evidence/model.spl` already
carried 8 of the 16 flagged `primitive_api` errors **before** this session's
edit (`selector_binary_field`'s `lsb`/`width`, `selector_byte_range`'s
`offset`/`length`, `check_numeric_tolerance`'s `tolerance`,
`evidence_node_at`'s `order`, and two bare-`bool` return types). The file was
never lint-clean; any future untouched edit to it would have hit the same
mandatory `lint-cached.shs` pre-push block this session hit, for reasons
unrelated to that edit. This session added 8 more of the same class
(`selector_pixel_region`'s 4 params, `pixel_region_x/y/width/height`'s 4
return types) when closing the `pixel_region` selector gap — see
`doc/03_plan/infra/llm_fraud_prevention/rules_sdl_anti_fraud_plan.md`.

## Why this session pushed past it with `--no-verify`

Redesigning the public selector/oracle API in `model.spl` with typed wrappers
to satisfy the rule properly is real scope beyond the fraud-prevention task,
and risks breaking every other spec that already calls these functions with
today's bare-`i64`/`bool` signatures. Implementing the missing allow-attr
plumbing is itself non-trivial, touches shared lint infrastructure used
repo-wide, and is not something to rush under time pressure. The user
explicitly approved a one-time `--no-verify` push for this specific range
rather than either of those under-time-pressure options, with this bug filed
so the debt is tracked rather than hidden.

## Resume plan

1. Implement file-level `#![allow(RULE)]` / statement-level `@allow(RULE)`
   suppression as shared machinery in the lint pipeline (likely
   `semantic_api/checker.spl` threading attribute state into each rule's
   `check_module_items`/`check_function`), then verify against the physics
   files that already assume it works.
2. Once suppression is real, decide per-file whether to keep the annotation
   (accepting bare primitives as intentional for a geometry/bit-layout
   module) or to actually introduce typed wrappers for
   `src/lib/common/spec/evidence/model.spl`'s selector/oracle API.
3. Re-run `sh scripts/check/lint-cached.shs src/lib/common/spec/evidence/model.spl`
   and confirm `PASS` before removing this bug's OPEN status.
