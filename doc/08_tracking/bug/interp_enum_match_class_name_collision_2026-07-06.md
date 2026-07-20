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

## New instance (2026-07-20): `Fat32Core` import-alias vs. real class — `unknown static method new`

Found while repairing `test/01_unit/os/desktop/wm_pointer_decode_spec.spl`
(SPEC-REPAIR lane). Any spec that transitively compiles the full
`src/os/desktop/shell.spl` module graph (e.g.
`test/01_unit/os/desktop/shell_wm_runtime_loop_spec.spl`) fails at semantic
analysis with:

```
error: semantic: unknown static method new on class Fat32Core
error: test-runner: no examples executed
```

with no file:line attached to the diagnostic. Root cause is the same
duplicate-symbol-name class as above, via an **import alias** rather than two
same-named classes:

- `src/os/services/vfs/vfs_boot_init.spl:21` imports
  `use os.services.fat32.shared_fat32_driver.{SharedFat32Driver as Fat32Core}`
  and calls `Fat32Core.new(g_adapter)` at lines 97, 379, 1289 — here
  `Fat32Core` is an **alias** for `SharedFat32Driver`
  (`src/os/services/fat32/shared_fat32_driver.spl:13`, which does have
  `static fn new(device: BlockDevice) -> SharedFat32Driver` at line 21).
- `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl:14` (and the
  `nogc_async_mut` sibling) imports the **real, unaliased**
  `use std.fs_driver.fat32_core.{Fat32Core, OpenFile}` — the actual
  `Fat32Core` class (`src/lib/nogc_sync_mut/fs_driver/fat32_core.spl:74`,
  `static fn new(device: BlockDevice) -> Fat32Core` at line 100) — and calls
  `Fat32Core.new(device)` itself (lines 27, 35, 43, 387, 396).

Both files are reachable in the same compiled program from
`shell.spl` → `os.services.launcher.launcher` / VFS init → `vfs_boot_init.spl`
+ `fat32_stub.spl`. The global (non-module-scoped) class/static-method
registry collides the alias binding `Fat32Core = SharedFat32Driver` with the
real `class Fat32Core`, and the merged entry's static-method table does not
resolve `new` — even though **both** underlying types genuinely have a
`static fn new`. This is not a missing method; it's the same
alias-vs-real-class collision bug as the `Logger` case above, one level
removed (via `as Fat32Core` rather than two files independently defining
`class Fat32Core`).

**Verified NOT caused by the SPEC-REPAIR module split**: `shell.spl` was only
touched to remove two pure decode helpers (`wm_pointer_button_from_code`,
`wm_pointer_kind_from_code`, previously at shell.spl:224-250) into a new
standalone `src/os/desktop/wm_pointer_decode.spl`, replacing them with an
`use os.desktop.wm_pointer_decode.{...}` import at shell.spl:48 — nothing
touching VFS/Fat32/launcher. `wm_pointer_decode_spec.spl` now imports only
the new standalone module and is unaffected (11/11 green, no VFS in its
import graph). `shell_wm_runtime_loop_spec.spl` (and presumably other specs
that pull in the full `shell.spl` graph) remain blocked by this pre-existing
collision, independent of and unrelated to the module split.

Suggested fix: same as above (module-scoped class/static-method resolution),
plus specifically: alias bindings (`use X.{Y as Z}`) must not merge into the
global symbol table under the alias name `Z` if a real `class Z` exists
elsewhere in the compiled graph — alias resolution should stay lexically
scoped to the importing file.
