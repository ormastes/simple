# lifecycle_spec

> Purpose: Prove that extension lifecycle: activate -> dispatch -> deactivate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_spec

Purpose: Prove that extension lifecycle: activate -> dispatch -> deactivate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/extensions/lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that extension lifecycle: activate -> dispatch -> deactivate.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### extension lifecycle: activate -> dispatch -> deactivate

#### dispatch_command lazily activates the owner then runs the handler

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatch_command lazily activates the owner then runs the handler
- Verify: dispatch_command lazily activates the owner then runs the handler
   - Expected: host.is_active("demo-ext") is false
   - Expected: out equals `ran:world`
   - Expected: "dispatch" equals `failed`
   - Expected: host.is_active("demo-ext") is true
   - Expected: host.lifetime_disposable_count("demo-ext") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatch_command lazily activates the owner then runs the handler")
step("Verify: dispatch_command lazily activates the owner then runs the handler")
# @req: REQ-LIB-EDITOR-001
val host = ExtensionHost.new()
host.register_manifest(lifecycle_demo_manifest(), "<test>")
host.register_command_handler("demo-ext", "demo.hello", "Demo Hello", lifecycle_handler)
expect(host.is_active("demo-ext")).to_equal(false)
match host.dispatch_command("demo.hello", "world"):
    case Ok(out):
        expect(out).to_equal("ran:world")
    case Err(_):
        expect("dispatch").to_equal("failed")
expect(host.is_active("demo-ext")).to_equal(true)
expect(host.lifetime_disposable_count("demo-ext")).to_equal(1)
```

</details>

#### deactivation disposes all registrations and dispatch fails cleanly

- deactivation disposes all registrations and dispatch fails cleanly
- Verify: deactivation disposes all registrations and dispatch fails cleanly
   - Expected: host.lifetime_disposable_count("demo-ext") equals `2`
   - Expected: out equals `ran:x`
   - Expected: "dispatch" equals `failed`
   - Expected: host.deactivate("demo-ext") is true
   - Expected: host.lifetime_disposable_count("demo-ext") equals `0`
   - Expected: host.command_handler_registered("demo.hello") is false
   - Expected: "dispatch after deactivate" equals `should fail`
   - Expected: e contains `no handler registered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("deactivation disposes all registrations and dispatch fails cleanly")
step("Verify: deactivation disposes all registrations and dispatch fails cleanly")
val host = ExtensionHost.new()
host.register_manifest(lifecycle_demo_manifest(), "<test>")
host.register_command_handler("demo-ext", "demo.hello", "Demo Hello", lifecycle_handler)
host.on_event("demo-ext", "doc.saved", lifecycle_listener)
expect(host.lifetime_disposable_count("demo-ext")).to_equal(2)
match host.dispatch_command("demo.hello", "x"):
    case Ok(out):
        expect(out).to_equal("ran:x")
    case Err(_):
        expect("dispatch").to_equal("failed")
expect(host.deactivate("demo-ext")).to_equal(true)
expect(host.lifetime_disposable_count("demo-ext")).to_equal(0)
expect(host.command_handler_registered("demo.hello")).to_equal(false)
match host.dispatch_command("demo.hello", "again"):
    case Ok(_):
        expect("dispatch after deactivate").to_equal("should fail")
    case Err(e):
        expect(e.contains("no handler registered")).to_equal(true)
```

</details>

#### typed event listeners are invoked and counted by emit_event

- typed event listeners are invoked and counted by emit_event
- Verify: typed event listeners are invoked and counted by emit_event
   - Expected: host.emit_event("doc.saved", "payload") >= 1 is true
   - Expected: host.emit_event("doc.saved", "payload") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("typed event listeners are invoked and counted by emit_event")
step("Verify: typed event listeners are invoked and counted by emit_event")
val host = ExtensionHost.new()
host.register_manifest(lifecycle_demo_manifest(), "<test>")
host.activate("demo-ext")
host.on_event("demo-ext", "doc.saved", lifecycle_listener)
expect(host.emit_event("doc.saved", "payload") >= 1).to_equal(true)
host.deactivate("demo-ext")
expect(host.emit_event("doc.saved", "payload")).to_equal(0)
```

</details>

#### dispatching a command nobody declared or registered fails cleanly

- dispatching a command nobody declared or registered fails cleanly
- Verify: dispatching a command nobody declared or registered fails cleanly
   - Expected: "ghost dispatch" equals `should fail`
   - Expected: e contains `no handler registered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatching a command nobody declared or registered fails cleanly")
step("Verify: dispatching a command nobody declared or registered fails cleanly")
val host = ExtensionHost.new()
match host.dispatch_command("ghost.cmd", "x"):
    case Ok(_):
        expect("ghost dispatch").to_equal("should fail")
    case Err(e):
        expect(e.contains("no handler registered")).to_equal(true)
```

</details>

#### builtins register (unactivated) and activate lazily through their own declared events, without wildcard activation

- builtins register (unactivated) and activate lazily through their own declared events, without wildcard activation
- Verify: builtins register (unactivated) and activate lazily through their own declared events, without wildcard activation
   - Expected: host.is_active("simple-language") is false
   - Expected: host.is_active("markdown-language") is false
   - Expected: host.is_active("sdn-graph-language") is false
   - Expected: host.command_registered("markdown.toggle_bold") is false
   - Expected: host.find_language_for_ext(".md") equals ``
   - Expected: host.activate_language("markdown") equals `1`
   - Expected: host.is_active("markdown-language") is true
   - Expected: host.command_registered("markdown.toggle_bold") is true
   - Expected: host.find_language_for_ext(".md") equals `markdown`
   - Expected: host.is_active("simple-language") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builtins register (unactivated) and activate lazily through their own declared events, without wildcard activation")
step("Verify: builtins register (unactivated) and activate lazily through their own declared events, without wildcard activation")
val host = extension_host_with_builtins()
expect(host.extension_count()).to_be_greater_than(2)
expect(host.is_active("simple-language")).to_equal(false)
expect(host.is_active("markdown-language")).to_equal(false)
expect(host.is_active("sdn-graph-language")).to_equal(false)
expect(host.command_registered("markdown.toggle_bold")).to_equal(false)
expect(host.find_language_for_ext(".md")).to_equal("")
expect(host.activate_language("markdown")).to_equal(1)
expect(host.is_active("markdown-language")).to_equal(true)
expect(host.command_registered("markdown.toggle_bold")).to_equal(true)
expect(host.find_language_for_ext(".md")).to_equal("markdown")
# A matching event does not drag unrelated builtins up with it.
expect(host.is_active("simple-language")).to_equal(false)
```

</details>

#### the indexed builtin host activates nothing and registers no contributions

- the indexed builtin host activates nothing and registers no contributions
- Verify: the indexed builtin host activates nothing and registers no contributions
   - Expected: host.active_count() equals `0`
   - Expected: host.is_active("markdown-language") is false
   - Expected: host.is_active("simple-language") is false
   - Expected: host.command_registered("markdown.toggle_bold") is false
   - Expected: host.find_language_for_ext(".md") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the indexed builtin host activates nothing and registers no contributions")
step("Verify: the indexed builtin host activates nothing and registers no contributions")
val host = extension_host_with_builtins_indexed()
expect(host.extension_count()).to_be_greater_than(2)
expect(host.active_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(host.is_active("markdown-language")).to_equal(false)
expect(host.is_active("simple-language")).to_equal(false)
expect(host.command_registered("markdown.toggle_bold")).to_equal(false)
expect(host.find_language_for_ext(".md")).to_equal("")
```

</details>

#### an indexed builtin activates lazily through its declared onLanguage event

- an indexed builtin activates lazily through its declared onLanguage event
- Verify: an indexed builtin activates lazily through its declared onLanguage event
   - Expected: host.activate_language("markdown") equals `1`
   - Expected: host.is_active("markdown-language") is true
   - Expected: host.command_registered("markdown.toggle_bold") is true
   - Expected: host.find_language_for_ext(".md") equals `markdown`
   - Expected: host.activate_language("markdown") equals `0`
   - Expected: host.is_active("simple-language") is false
   - Expected: host.active_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an indexed builtin activates lazily through its declared onLanguage event")
step("Verify: an indexed builtin activates lazily through its declared onLanguage event")
val host = extension_host_with_builtins_indexed()
expect(host.activate_language("markdown")).to_equal(1)
expect(host.is_active("markdown-language")).to_equal(true)
expect(host.command_registered("markdown.toggle_bold")).to_equal(true)
expect(host.find_language_for_ext(".md")).to_equal("markdown")
# idempotent: the same event has nothing left to activate
expect(host.activate_language("markdown")).to_equal(0)
# and it did NOT drag its neighbours up with it
expect(host.is_active("simple-language")).to_equal(false)
expect(host.active_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### an indexed builtin activates lazily through its declared onCommand event

- an indexed builtin activates lazily through its declared onCommand event
- Verify: an indexed builtin activates lazily through its declared onCommand event
   - Expected: host.is_active("writer") is false
   - Expected: host.activate_command("writer.save") equals `1`
   - Expected: host.is_active("writer") is true
   - Expected: host.command_registered("writer.format_bold") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an indexed builtin activates lazily through its declared onCommand event")
step("Verify: an indexed builtin activates lazily through its declared onCommand event")
val host = extension_host_with_builtins_indexed()
expect(host.is_active("writer")).to_equal(false)
expect(host.activate_command("writer.save")).to_equal(1)
expect(host.is_active("writer")).to_equal(true)
expect(host.command_registered("writer.format_bold")).to_equal(true)
```

</details>

#### a theme contributed by a builtin is resolvable through the host once that builtin activates

- a theme contributed by a builtin is resolvable through the host once that builtin activates
- Verify: a theme contributed by a builtin is resolvable through the host once that builtin activates
   - Expected: host.theme_registered("aetheric-dark") is false
   - Expected: host.activate_command("designer.load_note") equals `1`
   - Expected: host.is_active("designer") is true
   - Expected: host.theme_registered("aetheric-dark") is true
   - Expected: entry.extension_name equals `designer`
   - Expected: entry.theme.ui_theme equals `dark`
   - Expected: entry.theme.path equals `config/themes/aetheric_dark/theme.sdn`
   - Expected: host.theme_registered("no-such-theme") is false
   - Expected: host.find_theme("no-such-theme").extension_name equals ``
   - Expected: host.deactivate("designer") is true
   - Expected: host.theme_registered("aetheric-dark") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a theme contributed by a builtin is resolvable through the host once that builtin activates")
step("Verify: a theme contributed by a builtin is resolvable through the host once that builtin activates")
val host = extension_host_with_builtins()
expect(host.theme_registered("aetheric-dark")).to_equal(false)
expect(host.activate_command("designer.load_note")).to_equal(1)
expect(host.is_active("designer")).to_equal(true)
expect(host.theme_registered("aetheric-dark")).to_equal(true)
val entry = host.find_theme("aetheric-dark")
expect(entry.extension_name).to_equal("designer")
expect(entry.theme.ui_theme).to_equal("dark")
expect(entry.theme.path).to_equal("config/themes/aetheric_dark/theme.sdn")
# an id nobody declared stays unresolved
expect(host.theme_registered("no-such-theme")).to_equal(false)
expect(host.find_theme("no-such-theme").extension_name).to_equal("")
# deactivation reverses the contribution, like every other kind
expect(host.deactivate("designer")).to_equal(true)
expect(host.theme_registered("aetheric-dark")).to_equal(false)
```

</details>

#### extension_host_with_builtins() and extension_host_with_builtins_indexed() index the same manifests, both unactivated

- extension_host_with_builtins() and extension_host_with_builtins_indexed() index the same manifests, both unactivated
- Verify: extension_host_with_builtins() and extension_host_with_builtins_indexed() index the same manifests, both unactivated
   - Expected: indexed.extension_count() equals `eager.extension_count()`
   - Expected: eager.active_count() equals `0`
   - Expected: indexed.active_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extension_host_with_builtins() and extension_host_with_builtins_indexed() index the same manifests, both unactivated")
step("Verify: extension_host_with_builtins() and extension_host_with_builtins_indexed() index the same manifests, both unactivated")
val eager = extension_host_with_builtins()
val indexed = extension_host_with_builtins_indexed()
expect(indexed.extension_count()).to_equal(eager.extension_count())
expect(eager.active_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(indexed.active_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-EDITOR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6e5f1fb95a9cebb9c1acaf7e686895c4e1f16b57d9df659335dae3916f0141b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6e5f1fb95a9cebb9c1acaf7e686895c4e1f16b57d9df659335dae3916f0141b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6e5f1fb95a9cebb9c1acaf7e686895c4e1f16b57d9df659335dae3916f0141b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/editor/extensions/lifecycle_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/extensions/lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/extensions/lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/extensions/lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/extensions/lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/editor/extensions/lifecycle_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatch_command lazily activates the owner then runs the handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/extensions/lifecycle_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deactivation disposes all registrations and dispatch fails cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/extensions/lifecycle_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'typed event listeners are invoked and counted by emit_event' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
