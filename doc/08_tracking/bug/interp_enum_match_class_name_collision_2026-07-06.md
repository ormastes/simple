# Interpreter: enum-variant match returns nil when a class shares the variant name (closure-dependent)

- **Date:** 2026-07-06
- **Area:** interpreter (self-hosted deployed binary, interpret mode)
- **Severity:** high (silent nil poisoning, closure-dependent — passes in unit repros, fails in apps)

## Symptom

`capability_name(cap)` in `src/lib/common/ui/capability_policy.spl` returns nil
for `Capability.Color` (and only for `Color`) when executed inside the
`src/app/ui.browser/main.spl --open` import closure. The nil then crashes JSON
serialization with:

```
error: semantic: method `replace` not found on type `nil` (receiver value: nil)
```

Field-probe evidence from the app run (2026-07-06):

```
DBGPROBE: cap0 name=Mouse value=true
DBGPROBE: cap1 name=nil value=true      <- Capability.Color
DBGPROBE: cap2 name=Images value=true
DBGPROBE: cap3 name=Touch value=true
```

## Closure dependence (key evidence)

The identical call chain
(`web_render_capabilities_for_target(WEB_RENDER_TARGET_PURE_SIMPLE)` →
`semantic_ui_snapshot_from_state_with_capabilities` →
`semantic_ui_snapshot_to_json`) run from a SMALL standalone script returns
`name=Color` correctly and serializes fine. Only inside the browser app's
large import closure does the `Capability.Color` match arm miss. The browser
closure (unlike the small repro) imports several classes named `Color`
(ui color model / gpu engine2d), strongly suggesting the interpreter resolves
the qualified enum pattern `Capability.Color` against the wrong `Color` symbol
when both are in scope.

## Workaround in place

`src/lib/common/ui/semantic_contract.spl` /
`semantic_ui_capabilities_from_backend` guards the name with `?? ""` so a nil
capability name cannot crash `escape_json`. The Color capability then
serializes with an empty name — cosmetic loss, no crash. Remove the guard
comment reference when this bug is fixed.

## Repro

1. `SIMPLE_GUI=1 SIMPLE_EXECUTION_MODE=interpret SIMPLE_LIB=src bin/simple src/app/ui.browser/main.spl examples/06_io/ui/hello_web.ui.sdn --open --backend=metal` (before the workaround) — crash at `backend.spl` render_frame snapshot serialization.
2. Same functions from a minimal script — no crash, `name=Color` correct.

## Suspected fix area

Interpreter pattern resolution for qualified enum-variant patterns
(`Enum.Variant:` match arms) must resolve `Variant` within the enum's own
namespace before falling back to imported type names.

## New instance (2026-07-11): duplicate class NAMES across modules — `Logger`

Loading `app.io.mod` (→ `src/compiler/00.common/config.spl`, which constructs
its own `Logger(level: ...)`) together with the JS engine
(`std.js.engine.js_error.Logger`, fields `(name)`) in one interpreter graph
fails SEMANTIC analysis with `class Logger has no field named level` — the
compiler-config construction resolves against the js-engine Logger. Four
distinct `Logger` classes exist (`js_error`, `browser_engine/shared/logging`,
`common/web/logging`, compiler config); which one wins appears to be
load-order dependent. Workaround used in probes: avoid importing `app.io.mod`
into graphs that load the JS engine (raw `rt_file_read_text` extern instead).
Real fix should make interpreter class resolution module-scoped.
