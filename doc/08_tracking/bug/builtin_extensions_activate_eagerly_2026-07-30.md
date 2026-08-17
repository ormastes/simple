# Builtin extensions activate eagerly, defeating lazy activation

- **Found:** 2026-07-30, while replacing source-text assertions in
  `test/01_unit/lib/editor/extension_discovery_contract_spec.spl`
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  local WC confirmed byte-identical on every file cited below). All three
  "Fix direction" steps landed: (1) `sheets_ext`/`slides_ext` manifests now
  declare `onCommand:<their own command id>` alongside their original
  registry-publish event, and `formula.spl`/`slide.spl`/`slides_app.spl` call
  the new `extension_host_ensure_command_activated(command_id)` seam
  (`src/lib/editor/extensions/host.spl`) before reading their process-global
  registries — the "at minimum" alternative to a full typed provider handle,
  not the typed-handle rewrite itself; (2) `capabilities.spl` calls
  `host.activate_command(command_id)` before the `is_active` gate; (3) the
  eager `_extension_host_activate_all_builtins` loop and its call site are
  deleted outright (not just unused) from `extension_host_with_builtins()`,
  which is now identical to `extension_host_with_builtins_indexed()`, and
  `extension_discovery_contract_spec.spl` was updated accordingly. Re-verified
  empirically 2026-07-31 (lane S2) with a standalone `bin/simple run` probe:
  an unrelated `activate_language("markdown")` does NOT wake the sheets
  builtin, while `activate_command("sheets.function.double")` /
  `activate_command("slides.layout.titleDiagram")` — and the real call-site
  path, `extension_host_ensure_command_activated(...)` — both do. Spec
  `activation_hook_spec.spl` gained a new describe block asserting exactly
  this ("fixed 2026-07-31") and passes 10/10. The CRITICAL sub-issue below
  (self-fulfilling `bound` probe) is also **FIXED 2026-07-31** — see the note
  at the top of that section. The historical record below (as found
  2026-07-30) is kept for context; read the FIXED notes, not the original
  claims, for current status. The "Adjacent, not fixed here" section
  (keybindings sink, themes, custom editors) is unrelated scope and remains
  open as its own, separately tracked gap.

## CRITICAL: `bound` is a self-fulfilling probe, not proof anything works

**FIXED 2026-07-31.** `_ide_capability_with_live_state`
(`src/app/ide/capabilities.spl`) no longer registers `_ide_capability_probe_handler`
at all -- that function and the registration call are deleted. The gate is now
a pure read: `if host.command_handler_registered(command_id): state = "bound"`.
Measured effect on `ide_capabilities_live()`, same synced tree, same run:
before = 11 of 11 capabilities report `bound`; after = 0 of 11 (all cap at
`activatable`). That is the expected, correct outcome, not a regression: no
builtin extension registers a real `CommandRegistry` handler on the host
`ide_capabilities_live()` builds (the five markdown handlers in
`editor_controller.spl` are registered on a separate, app-owned host
instance, never on the one the census inspects).

**Update (same day, follow-up fix): the split host is now closed, and the
census reads 1 bound / 10 activatable.** The handler registrations moved out
of `EditorController.new()` into
`extension_host_with_builtin_handlers()` (`src/lib/editor/extensions/host.spl`),
which both the editor and the census now call — so the census inspects the
same dispatchable host the editor runs on, instead of a throwaway. markdown
reaches `bound` through its own real handler; the other ten builtins
contribute no handler and correctly stay `activatable`.

One extra defect surfaced while wiring it: the probe only ever asked about
`contributes_commands[0]`. markdown declares `md.preview` first (a view
command with no handler) while its five real handlers sit on
`markdown.toggle_bold` and friends — so index-0 probing would have reported
the whole extension unbound purely because of manifest ordering. `bound` now
asks whether ANY contributed command has a handler, and `feature_check`
names the one that satisfied it.

`test/01_unit/app/ide/capability_truth_spec.spl` asserts this directly:
markdown is `bound` with `check=markdown.toggle_bold`, and the anti-self-probe
guard is now (a) an exact bound-count of 1 — the original defect's signature
was every capability flipping at once — and (b) the absence of the probe's own
`"capability truth probe"` title string from the report. The historical record
of the original defect (as found 2026-07-30) is kept below for context.

Verified directly in `src/app/ide/capabilities.spl:213-215`
(`_ide_capability_with_live_state`):

```
host.register_command_handler(m.name, command_id, "capability truth probe: " + cap.id, _ide_capability_probe_handler)
if host.command_handler_registered(command_id):
    state = "bound"
```

This **registers a probe handler and then asks the registry whether that
handler is registered** — a write-then-check-your-own-write. It proves the
command id *can be bound through the real `CommandRegistry`* — the code's own
comment at line 169 says exactly that, "proves a command id CAN be bound" — it
is **not** evidence that any real caller ever invokes the command, nor that a
real handler backs it. The state name `bound` overstates what the check
establishes; read the comment, not the label.

Combined with eager builtin activation below, a builtin-backed capability is
nearly guaranteed to report `bound` regardless of merit: two independent
false-positive mechanisms stack on the same census number. Do not cite
"N of 11 bound" as evidence that a capability works end to end.

**2026-07-30, later same day — sheets case study, verification complete.**
`builtin/sheets_ext.spl` gained `ExtensionLanguage(id: "sheets", extensions:
[".xlsx", ".xls", ".csv"])`.
- Baseline (`origin/main`): `sheets -> declared (check=sheets.smoke)`, other
  10 capabilities `bound` (10 of 11).
- With the change: `sheets -> bound (check=sheets.function.double)`, 11 of 11.
- Mechanism: `.xlsx`/`.csv` extension strings substring-match the `xlsx`/`csv`
  compat tags in `_ide_manifest_matches_tag`, so `_ide_capability_manifest_for`
  now finds `sheets-function-registry-demo` where it previously matched
  nothing and fell through to a hardcoded `declared`.
- Honest framing (as of 2026-07-30, before Blocker 1 was fixed): this
  legitimately closed a **discoverability** gap — the manifest genuinely does
  back those file kinds now — but did **not** make activation real at the
  time. **Update, FIXED 2026-07-31:** `sheets-function-registry-demo` is no
  longer lazily-unreachable — see "Blocker 1" below, now fixed. Its command
  id (`sheets.function.double`) is itself a declared activation event, and
  `formula.spl` activates it before consulting the registry, so `bound` is
  now earned rather than cosmetic.
- Office suite spec with the change: `Results: 21 total, 21 passed, 0 failed`.

## What happens

**FIXED 2026-07-31** — this whole section describes the pre-fix behavior,
kept for historical context. `extension_host_with_builtins()` no longer
activates anything; it is now identical to `extension_host_with_builtins_indexed()`.

`extension_host_with_builtins()` (`src/lib/editor/extensions/host.spl`)
registers all 14 builtin manifests and then unconditionally activates every one.

Measured on a fresh host, before any activation event is sent:

```
pre  active=true cmd=true          # sdn-graph-language already active
activate_language("sdn-graph")=0   # nothing left to activate
direct activate("sdn-graph-language")=false
```

So for builtins there is no `onCommand:` / `onLanguage:` laziness at all: every
activation hook runs at construction, and every contributed command is
registered before anything asks for it.

## Why it matters

1. **The documented contract says otherwise.** `ide_office_plugin_suite.md`
   ("Startup reads manifests and builds indexes; plugin activation stays lazy")
   and the authoring guide's lazy-activation section are true only for the
   disk-discovered path.
2. **It makes the capability state machine degenerate.** `ide_capabilities_live()`
   distinguishes `declared → indexed → activatable → bound`, but since every
   builtin is pre-activated, builtin-backed capabilities can only ever report
   `bound`. This stacks with a second, independent false-positive mechanism —
   `bound` itself is a self-fulfilling write-then-check-your-own-write probe,
   not proof of a real caller — see "CRITICAL" section above. The census
   (10-of-11, now 11-of-11 after the sheets manifest change) is much weaker
   evidence than either number implies.
3. **Startup cost scales with builtin count**, which is the thing lazy
   activation exists to avoid — 14 today.
4. `activate_language()` / `activate_command()` return 0 for builtins even
   though the language/command is served. A caller treating the count as
   "did this work?" reads a false negative. `src/app/` calls `activate_language`
   10 times.

## Not a defect in

The disk-discovered path is genuinely lazy and proven so:
`extension_discovery_contract_spec.spl` shows a discovered extension inactive
with its command unregistered until `activate_command` fires, and the walking
skeleton (`test/03_system/ide/extension_kernel_walking_skeleton_spec.spl`) covers
discover-without-execution → activate → dispatch → dispose.

## Root cause of the block (measured 2026-07-30)

The host machinery is NOT the problem. Probing every builtin manifest's declared
activation events against the only two ways `activate_event` is ever reached
(`activate_language` → `onLanguage:`, `activate_command` → `onCommand:` — no
call site anywhere in `src/` passes a custom event string):

| | count | detail |
|---|---|---|
| lazily reachable | **12 of 14** | declare `onLanguage:` and/or `onCommand:` |
| lazily UNREACHABLE | **2 of 14** | `sheets-function-registry-demo`, `slides-layout-registry-demo` |

Simulating the lazy host (register manifests + hooks, no activate-all):

```
extension_count=14 active_count=0
activate_language(markdown)=1   activate_language(simple)=1   activate_language(sdn-graph)=1
activate_command(sheets.function.double)=0
activate_command(slides.layout.titleDiagram)=0
after: active_count=3 of 14
```

### Blocker 1 — the two registry builtins become permanently dead

**FIXED 2026-07-31.** Both manifests now additionally declare
`"onCommand:<their own contributed command id>"` as an activation event
(`sheets_ext.spl`: `["onFunctionRegistry:sheets", "onCommand:sheets.function.double"]`;
`slides_ext.spl` analogous for `slides.layout.titleDiagram`), and the readers
below now call the new singleton seam
`extension_host_ensure_command_activated(command_id)`
(`src/lib/editor/extensions/host.spl`) once before consulting their registry,
instead of reading it cold. This is the doc's own "at minimum" alternative
from the Fix direction section, not the typed-provider-handle rewrite — it
was judged sufficient because it makes the process-global-registry reads go
through a real `onCommand:` activation event without threading a handle
through `formula.spl`'s ~9.7k-line evaluator. The rest of this section is the
original (now-resolved) analysis, kept for context.

`sheets-function-registry-demo` declares exactly one activation event,
`onFunctionRegistry:sheets`; `slides-layout-registry-demo` declares
`onLayoutRegistry:slides`. **Nothing in `src/` ever emits either event**, and
neither manifest lists its own contributed command id
(`sheets.function.double` / `slides.layout.titleDiagram`) as an activation
event — so even `dispatch_command` cannot bring them up (it would fall through
to `Err("extension not active: ...")`).

Adding the missing `onCommand:` events would not fix it, because their activation
hooks publish into **process-global registries**:

- `sheets_ext_activation_hook` → `app.office.sheets.function_registry`, read
  directly by `src/app/office/sheets/formula.spl:3289,3302`
- `slides_ext_activation_hook` → `app.office.slides.layout_registry`, read
  directly by `src/app/office/slides/slide.spl:283` and
  `src/app/office/slides/slides_app.spl:57,134`

Neither reader holds an `ExtensionHost` or fires any event. There is no seam
through which "a formula needs function DOUBLE" or "the layout dropdown is being
built" can become an activation event. That is precisely the typed
provider-handle work this bug's fix direction called for.

### Blocker 2 — `ide_capabilities_live()` gates on `is_active` and never activates

**FIXED 2026-07-31.** `_ide_capability_with_live_state` now calls
`host.activate_command(command_id)` immediately before the `is_active` gate
(`src/app/ide/capabilities.spl:234-235` on `origin/main`). The rest of this
section is the original analysis, kept for context.

`_ide_capability_with_live_state` (`src/app/ide/capabilities.spl:211`) reads
`if command_id != "" and host.is_active(m.name)` and never calls
`activate_command`. Going lazy today would downgrade 10 of 11 capabilities from
`bound` to `indexed` while they remain genuinely activatable and bindable — a
false report, not a more honest one. The fix is one line in `capabilities.spl`
(`host.activate_command(command_id)` before the gate), which must land with the
lazy switch, not before it.

### Blocker 3 — a spec pins the eager behavior

**FIXED 2026-07-31.** That spec now asserts the opposite (lazy) semantics —
`is_active("sdn-graph-language") == false` until `activate_language("sdn-graph")`
is called, which then returns `1` — with a comment noting the flip and citing
this bug doc. The rest of this section is the original analysis, kept for
context.

`test/01_unit/lib/editor/extension_discovery_contract_spec.spl:66-73` asserts
`is_active("sdn-graph-language") == true` on a fresh `extension_host_with_builtins()`
and `activate_language("sdn-graph") == 0`. It must be updated in the same change.

## What landed instead (2026-07-30)

Behavior is byte-for-byte unchanged; the situation is now honest and cheap to fix.

- `src/lib/editor/extensions/host.spl` splits the constructor:
  - `extension_host_with_builtins_indexed()` — indexes all 14 manifests and
    wires all activation hooks, activating **nothing**. This is the genuinely
    lazy foundation and it works: 12 of 14 builtins come up through their own
    declared events.
  - `_extension_host_activate_all_builtins(host)` — the eager loop, alone, with
    the two blockers above written at the call site.
  - `extension_host_with_builtins()` — indexed + eager, as before.
- Specs pin the real semantics (previously nothing did):
  - `lifecycle_spec.spl` (+4): indexed host has 0 active and no contributions;
    a builtin activates through `onLanguage:` and through `onCommand:` without
    dragging its neighbours up; eager and indexed index the same manifests.
  - `activation_hook_spec.spl` (+3, new describe): no hook runs on the indexed
    host; **no activation event can reach the sheets/slides builtins** while
    direct `activate(name)` still can — the blocker, asserted; an unrelated
    language activation does not wake the sheets builtin.
  - `extension_kernel_walking_skeleton_spec.spl` (+1): a builtin obeys the same
    index → lazy activate → tear-down contract as the disk fixture, contrasted
    with the eager constructor.

Verification: lifecycle 9/9, activation_hook 10/10, registry 10/10,
extension_discovery_contract 6/6, walking skeleton 5/5;
`bin/simple run src/app/ide/main.spl --feature-check --tui` exit 0,
`capabilities: 11`, `ide_capabilities_live()` still 10 bound / 1 declared.

## Fix direction (unchanged, now scoped) — ALL THREE STEPS LANDED 2026-07-31

Three ordered steps, all needed together:

1. Give `sheets_ext` / `slides_ext` a **typed provider handle** resolved through
   the host instead of a process-global registry, so `formula.spl` /
   `slide.spl` / `slides_app.spl` go through a seam that can fire an activation
   event. (Or, at minimum, have those manifests declare their own
   `onCommand:` events and have the office apps activate before reading.)
2. Add `host.activate_command(command_id)` to `_ide_capability_with_live_state`
   before the `is_active` gate.
3. Delete the `_extension_host_activate_all_builtins(host)` call from
   `extension_host_with_builtins()` and update
   `extension_discovery_contract_spec.spl:66-73`.

## Adjacent, not fixed here

Status as of 2026-07-30, later same day (all measured against the working
copy; verify against `origin/main` before trusting line numbers, as other
lanes are landing in this same area):

- **`contributes_keybindings` is now bound, but the sink has no reader.**
  `host.spl` `_register_contributions` builds a `KeyBinding(key, command,
  mode:"", args:"")` per manifest entry, records it in a new
  `keybinding_registry: [ExtensionKeybindingEntry]`, and calls
  `keybinding_manager_add_override` into a **host-owned** `KeybindingManager`.
  `_unregister_contributions` filters the registry by owner and calls
  `_rebuild_keybinding_overrides()` to rebuild the manager from scratch
  (config preserved, surviving overrides replayed) — needed because
  `KeybindingManager.overrides` carries no owner tag. A query wrapper
  `keybinding_resolve(key, mode)` was added. `ExtensionKeybinding.when` (the
  context predicate) is dropped in the conversion — `KeyBinding` has no "when"
  concept. But `KeybindingManager` appears in only three places in the whole
  repo: its own definition (`src/lib/editor/core/keybinding_manager.spl`),
  this new host.spl code, and the new spec. `src/app/editor/editor_controller.spl`
  imports `std.editor.common.keybindings` and calls `default_keybindings()`
  only to render a keyboard-shortcuts panel — there is no key→command
  resolution through any config anywhere. So a contributed keybinding still
  cannot reach dispatch; this moves the gap from "parsed and dropped" to
  "parsed and stored where nothing reads it". Spec:
  `test/01_unit/lib/editor/keybinding_contribution_spec.spl`, 6/6 — it proves
  round-tripping through the sink, not that keybindings work end to end.
- **`contributes_themes`** is still decoded by `manifest_sdn.spl` and asserted
  in specs, but no builtin declares it and the host still has no sink. Parsed
  and dropped, unchanged.
- **`contributes_custom_editors`** is still declared by three builtins
  (`writer.rich_document_editor`, `sheets.grid`, `slides.canvas`, each with
  `document_kind` + `priority`) with no host routing. Another lane is binding
  this now — treat as in progress, not fixed, until that lane's own report
  lands.

The indexed/eager split above makes binding these *easier*, not harder: the
natural home for keybinding/theme/custom-editor registration is
`_register_contributions` (already called from `activate`, already reversed by
`_unregister_contributions`), and the specs give that path a lazy host to
assert against instead of a pre-activated one where registration timing is
unobservable.
