# CSS invalid display cascade system-test plan

## Scope

Prove that malformed later `display` declarations do not replace the last
supported valid value through either canonical declaration application path:

`HTML/CSS -> computed Style -> Web layout -> DrawIrComposition -> Engine2D`

The existing concrete display set plus `initial`, `unset`, `inherit`, and
author-origin `revert` are covered. `revert-layer` is excluded until the parser
retains layer provenance.

## Executable specification and manual

- `test/03_system/feature/web_platform/css/display_invalid_cascade_spec.spl`
- `doc/06_spec/03_system/feature/web_platform/css/display_invalid_cascade_spec.md`

The manual is hand-reviewed static documentation. Runtime and docgen PASS are
not claimed until the qualified pure-Simple CLI is available.

## Frozen scenario flow

1. `Resolve duplicate display declarations through both style paths`
2. `Keep hidden nodes out of canonical Draw IR`
3. `Render exact visible-control Engine2D pixels`

## Acceptance oracles

- Malformed later values retain the last valid declaration through dispatch
  and full paths.
- `initial`/`unset` compute to `block`; important `inherit` copies the parent;
  important `revert` restores the UA tag default.
- Hidden probes emit no command; the visible full-path control emits its exact
  canonical box.
- Engine2D skips zero commands and returns the exact 32-pixel framebuffer.

## Traceability

| Requirement | Scenario | Oracle | Status |
|---|---|---|---|
| REQ-WEB-BROWSER-003 | `should retain the last valid display through WebIR DrawIR and Engine2D` | computed display | Static candidate |
| REQ-WEB-BROWSER-004 | same | Draw IR admission and exact pixels | Static candidate |
| REQ-WEB-BROWSER-021 | same | modern step-based SSpec and mirrored manual | Static candidate |
