# IDE Extension Kernel — Walking Skeleton

> End-to-end proof that the extension kernel's landed pieces (manifest SDN decoder, `ExtensionHost`, `CommandRegistry`) compose into the walking skeleton the parallel-lane plan requires: a real fixture extension (`test/fixtures/ide_extensions/hello/`) is discovered without being executed, stays inactive until its command is dispatched, lazily activates and runs its typed handler, a duplicate registration loses to the first registrant, and deactivation tears every registration back down.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IDE Extension Kernel — Walking Skeleton

End-to-end proof that the extension kernel's landed pieces (manifest SDN decoder, `ExtensionHost`, `CommandRegistry`) compose into the walking skeleton the parallel-lane plan requires: a real fixture extension (`test/fixtures/ide_extensions/hello/`) is discovered without being executed, stays inactive until its command is dispatched, lazily activates and runs its typed handler, a duplicate registration loses to the first registrant, and deactivation tears every registration back down.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | IDE-EXT-KERNEL S5 |
| Category | Infrastructure |
| Status | In Progress |
| Requirements | doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md (S5) |
| Source | `test/03_system/ide/extension_kernel_walking_skeleton_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end proof that the extension kernel's landed pieces (manifest SDN
decoder, `ExtensionHost`, `CommandRegistry`) compose into the walking
skeleton the parallel-lane plan requires: a real fixture extension
(`test/fixtures/ide_extensions/hello/`) is discovered without being
executed, stays inactive until its command is dispatched, lazily activates
and runs its typed handler, a duplicate registration loses to the first
registrant, and deactivation tears every registration back down.

External-process entrypoint execution (spawning `extension.entry` inside a
sandboxed host) is future L6 work — see `ExtensionHost._dispatch_runtime_invocation`.
This walking skeleton simulates the fixture extension's own activation code by
registering its handler programmatically once the manifest has loaded, exactly
as a real extension host would after running the entry module.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `extension_manifest_load_with_diagnostics` | Loads + decodes `extension.sdn`, collecting every diagnostic instead of aborting on the first |
| `ExtensionHost.register_manifest` | Indexes a manifest without activating it |
| `ExtensionHost.register_command_handler` | Eager registration; the command only *runs* once its owner is active |
| `ExtensionHost.dispatch_command` | Lazily activates the owning extension (`onCommand:<id>`), then runs the real handler |
| `ExtensionHost.deactivate` | Disposes every registration the extension's lifetime owns |
| `extension_host_with_builtins_indexed` | Indexes the builtin manifests + hooks and activates nothing — builtins on the same lazy contract as disk extensions |
| `extension_host_with_builtins` | The shipped constructor: identical to `extension_host_with_builtins_indexed` -- indexed, nothing activated (see the builtin-laziness scenario below) |

## Related Specifications

- [manifest_sdn_spec.spl](../../01_unit/lib/editor/extensions/manifest_sdn_spec.spl) — decoder unit coverage
- [lifecycle_spec.spl](../../01_unit/lib/editor/extensions/lifecycle_spec.spl) — host lifecycle unit coverage

## Scenarios

### IDE extension kernel walking skeleton: fixture.hello

#### fixture manifest loads clean, with commands/keybindings/themes decoded

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fixture manifest loads clean, with commands/keybindings/themes decoded
   - Expected: load.ok is true
   - Expected: load.issues.len() equals `0`
   - Expected: m.name equals `FIXTURE_EXTENSION_NAME`
   - Expected: m.host equals `in_process`
   - Expected: m.contributes_commands.len() equals `1`
   - Expected: m.contributes_commands[0].id equals `FIXTURE_COMMAND_ID`
   - Expected: m.contributes_commands[0].title equals `Hello: Greet`
   - Expected: m.contributes_languages.len() equals `0`
   - Expected: m.contributes_keybindings.len() equals `1`
   - Expected: m.contributes_keybindings[0].command equals `FIXTURE_COMMAND_ID`
   - Expected: m.contributes_keybindings[0].key equals `ctrl+shift+h`
   - Expected: m.contributes_themes.len() equals `1`
   - Expected: m.contributes_themes[0].id equals `hello-light`
   - Expected: m.contributes_themes[0].ui_theme equals `light`
   - Expected: m.activation_events.len() equals `1`
   - Expected: m.activation_events[0] equals `onCommand:hello.greet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixture manifest loads clean, with commands/keybindings/themes decoded")
val load = load_fixture_manifest()
expect(load.ok).to_equal(true)
expect(load.issues.len()).to_equal(0)
val m = load.manifest
expect(m.name).to_equal(FIXTURE_EXTENSION_NAME)
expect(m.host).to_equal("in_process")
expect(m.contributes_commands.len()).to_equal(1)
expect(m.contributes_commands[0].id).to_equal(FIXTURE_COMMAND_ID)
expect(m.contributes_commands[0].title).to_equal("Hello: Greet")
expect(m.contributes_languages.len()).to_equal(0)
expect(m.contributes_keybindings.len()).to_equal(1)
expect(m.contributes_keybindings[0].command).to_equal(FIXTURE_COMMAND_ID)
expect(m.contributes_keybindings[0].key).to_equal("ctrl+shift+h")
expect(m.contributes_themes.len()).to_equal(1)
expect(m.contributes_themes[0].id).to_equal("hello-light")
expect(m.contributes_themes[0].ui_theme).to_equal("light")
expect(m.activation_events.len()).to_equal(1)
expect(m.activation_events[0]).to_equal("onCommand:hello.greet")
```

</details>

#### activates lazily on dispatch, runs the real handler, then tears down cleanly on deactivate

- activates lazily on dispatch, runs the real handler, then tears down cleanly on deactivate
   - Expected: host.command_handler_registered(FIXTURE_COMMAND_ID) is true
   - Expected: host.is_active(FIXTURE_EXTENSION_NAME) is false
   - Expected: host.is_active(FIXTURE_EXTENSION_NAME) is true
   - Expected: host.lifetime_disposable_count(FIXTURE_EXTENSION_NAME) equals `1`
   - Expected: host.deactivate(FIXTURE_EXTENSION_NAME) is true
   - Expected: host.lifetime_disposable_count(FIXTURE_EXTENSION_NAME) equals `0`
   - Expected: host.command_handler_registered(FIXTURE_COMMAND_ID) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("activates lazily on dispatch, runs the real handler, then tears down cleanly on deactivate")
val host = build_fixture_host()

# (b) handlers register eagerly; the owning extension is not active yet.
expect(host.command_handler_registered(FIXTURE_COMMAND_ID)).to_equal(true)
expect(host.is_active(FIXTURE_EXTENSION_NAME)).to_equal(false)

# (c) dispatch activates the extension lazily, then runs the handler.
val first = dispatch_greet(host, "world")
Then_dispatch_ok(first, "hello:world")
expect(host.is_active(FIXTURE_EXTENSION_NAME)).to_equal(true)
expect(host.lifetime_disposable_count(FIXTURE_EXTENSION_NAME)).to_equal(1)

# (e) deactivate disposes every registration; a second dispatch fails,
# not crashes.
expect(host.deactivate(FIXTURE_EXTENSION_NAME)).to_equal(true)
expect(host.lifetime_disposable_count(FIXTURE_EXTENSION_NAME)).to_equal(0)
expect(host.command_handler_registered(FIXTURE_COMMAND_ID)).to_equal(false)
val second = dispatch_greet(host, "again")
Then_dispatch_err_contains(second, "no handler registered")
```

</details>

#### a duplicate registration of hello.greet loses to the first registrant

- a duplicate registration of hello.greet loses to the first registrant
   - Expected: conflict.kind equals `command-conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a duplicate registration of hello.greet loses to the first registrant")
val host = build_fixture_host()
val conflict = register_conflicting_handler(host)
expect(conflict.kind).to_equal("command-conflict")
# The original registration is untouched: dispatch still activates
# the real owner and runs the ORIGINAL handler, not the intruder's.
val result = dispatch_greet(host, "still-owned")
Then_dispatch_ok(result, "hello:still-owned")
```

</details>

#### a builtin obeys the same index -> lazy activate -> tear down contract as the fixture

- a builtin obeys the same index -> lazy activate -> tear down contract as the fixture
   - Expected: host.active_count() equals `0`
   - Expected: host.command_registered("markdown.toggle_bold") is false
   - Expected: host.activate_command("markdown.toggle_bold") equals `1`
   - Expected: host.is_active("markdown-language") is true
   - Expected: host.command_registered("markdown.toggle_bold") is true
   - Expected: host.find_language_for_ext(".md") equals `markdown`
   - Expected: host.deactivate("markdown-language") is true
   - Expected: host.command_registered("markdown.toggle_bold") is false
   - Expected: host.find_language_for_ext(".md") equals ``
   - Expected: shipped.active_count() equals `0`
   - Expected: shipped.activate_command("markdown.toggle_bold") equals `1`
   - Expected: shipped.is_active("markdown-language") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a builtin obeys the same index -> lazy activate -> tear down contract as the fixture")
# The disk fixture above proves the contract for discovered extensions.
# Builtins get the identical contract from the indexed constructor;
# extension_host_with_builtins() is now the same lazy contract (the
# eager activate-all loop was removed 2026-07-31 -- builtin
# capabilities are no longer already-active before any event fires).
# doc/08_tracking/bug/builtin_extensions_activate_eagerly_2026-07-30.md
val host = extension_host_with_builtins_indexed()
expect(host.extension_count()).to_be_greater_than(2)
expect(host.active_count()).to_equal(0)
expect(host.command_registered("markdown.toggle_bold")).to_equal(false)

expect(host.activate_command("markdown.toggle_bold")).to_equal(1)
expect(host.is_active("markdown-language")).to_equal(true)
expect(host.command_registered("markdown.toggle_bold")).to_equal(true)
expect(host.find_language_for_ext(".md")).to_equal("markdown")

expect(host.deactivate("markdown-language")).to_equal(true)
expect(host.command_registered("markdown.toggle_bold")).to_equal(false)
expect(host.find_language_for_ext(".md")).to_equal("")

# extension_host_with_builtins() (the shipped constructor) shares the
# identical lazy contract with the indexed constructor above.
val shipped = extension_host_with_builtins()
expect(shipped.active_count()).to_equal(0)
expect(shipped.activate_command("markdown.toggle_bold")).to_equal(1)
expect(shipped.is_active("markdown-language")).to_equal(true)
```

</details>

#### a broken manifest missing extension.id reports a diagnostic with line info

- a broken manifest missing extension.id reports a diagnostic with line info
   - Expected: load.ok is false
   - Expected: found_line >= 1 is true
   - Expected: dup_found is true
   - Expected: dup_line equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a broken manifest missing extension.id reports a diagnostic with line info")
# No '{' in this fixture text, so plain double-quoted concatenation
# is safe (the raw '...' landmine only bites once braces appear —
# see the fixture's inline command/keybinding/theme maps above).
val broken =
    "extension:\n" +
    "  schema: simple.ide.extension/1\n" +
    "  version: 1.0.0\n" +
    "  version: 2.0.0\n"
val load = extension_manifest_decode(broken)
expect(load.ok).to_equal(false)
var found_line = -1
for issue in load.issues:
    if issue.path == "extension.id" and issue.message.contains("missing required field"):
        found_line = issue.line
expect(found_line >= 1).to_equal(true)

# The duplicate `version:` key is also surfaced (parser-detected
# duplicate_key diagnostic, merged in with real line info).
var dup_found = false
var dup_line = -1
for issue in load.issues:
    if issue.path == "extension.version" and issue.message.contains("duplicate key"):
        dup_found = true
        dup_line = issue.line
expect(dup_found).to_equal(true)
expect(dup_line).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md (S5)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-IDE-EXT-KERNEL-S5`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f0f25cda4bc56ba87bf146eec237f3ce1800cc1e6a364516f3605fe0c84d1763`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0f25cda4bc56ba87bf146eec237f3ce1800cc1e6a364516f3605fe0c84d1763`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0f25cda4bc56ba87bf146eec237f3ce1800cc1e6a364516f3605fe0c84d1763`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/ide/extension_kernel_walking_skeleton_spec.spl
mirror: doc/06_spec/03_system/ide/extension_kernel_walking_skeleton_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/ide/extension_kernel_walking_skeleton_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/ide/extension_kernel_walking_skeleton_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/ide/extension_kernel_walking_skeleton_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/ide/extension_kernel_walking_skeleton_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/ide/extension_kernel_walking_skeleton_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixture manifest loads clean, with commands/keybindings/themes decoded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ide/extension_kernel_walking_skeleton_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'activates lazily on dispatch, runs the real handler, then tears down cleanly on deactivate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ide/extension_kernel_walking_skeleton_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a duplicate registration of hello.greet loses to the first registrant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
