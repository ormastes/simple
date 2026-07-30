# Builtin extensions activate eagerly, defeating lazy activation

- **Found:** 2026-07-30, while replacing source-text assertions in
  `test/01_unit/lib/editor/extension_discovery_contract_spec.spl`
- **Status:** OPEN. Behavior left as-is (app code depends on it); documented and
  filed rather than changed under a verification pass.

## What happens

`extension_host_with_builtins()` (`src/lib/editor/extensions/host.spl:705-714`)
registers all 14 builtin manifests and then unconditionally activates every one:

```
    for manifest in builtins:
        host.activate(manifest.name)
```

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
   `bound`. The 10-of-11-bound census is therefore weaker evidence than it looks.
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

## Fix direction

Drop the eager loop and let builtins activate through their declared events like
any other extension. Blockers to check first: `ide_capabilities_live()` computes
`bound` from live host state, and Writer/Sheets/Slides register formula
functions, layouts and element kinds from activation hooks — anything reading
those without first dispatching a command or opening a language would regress.
So this needs the provider-handle/typed-provider work, not a one-line deletion.
