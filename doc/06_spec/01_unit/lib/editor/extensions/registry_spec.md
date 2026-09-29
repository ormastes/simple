# registry_spec

> Purpose: Prove that CommandRegistry typed handlers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# registry_spec

Purpose: Prove that CommandRegistry typed handlers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/extensions/registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that CommandRegistry typed handlers.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### CommandRegistry typed handlers

#### executes the registered typed handler

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes the registered typed handler
- Verify: executes the registered typed handler
   - Expected: d.kind equals `command`
   - Expected: d.owner equals `ext-a`
   - Expected: reg.has("a.run") is true
   - Expected: out equals `ran:hi`
   - Expected: "handler ran" equals `handler failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes the registered typed handler")
step("Verify: executes the registered typed handler")
# @req: REQ-LIB-EDITOR-001
val reg = CommandRegistry.new()
val d = reg.register("ext-a", "a.run", "Run A", registry_spec_ok_handler)
expect(d.kind).to_equal("command")
expect(d.owner).to_equal("ext-a")
expect(reg.has("a.run")).to_equal(true)
match reg.run("a.run", "hi"):
    case Ok(out):
        expect(out).to_equal("ran:hi")
    case Err(_):
        expect("handler ran").to_equal("handler failed")
```

</details>

#### propagates handler errors as Err

- propagates handler errors as Err
- Verify: propagates handler errors as Err
   - Expected: "should fail" equals `but succeeded`
   - Expected: e equals `boom:x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates handler errors as Err")
step("Verify: propagates handler errors as Err")
val reg = CommandRegistry.new()
reg.register("ext-a", "a.fail", "Fail", registry_spec_err_handler)
match reg.run("a.fail", "x"):
    case Ok(_):
        expect("should fail").to_equal("but succeeded")
    case Err(e):
        expect(e).to_equal("boom:x")
```

</details>

#### running an unregistered command fails cleanly

- running an unregistered command fails cleanly
- Verify: running an unregistered command fails cleanly
   - Expected: "should fail" equals `but succeeded`
   - Expected: e contains `no handler registered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("running an unregistered command fails cleanly")
step("Verify: running an unregistered command fails cleanly")
val reg = CommandRegistry.new()
match reg.run("no.such", "x"):
    case Ok(_):
        expect("should fail").to_equal("but succeeded")
    case Err(e):
        expect(e.contains("no handler registered")).to_equal(true)
```

</details>

#### duplicate command id: first wins, conflict recorded

- duplicate command id: first wins, conflict recorded
- Verify: duplicate command id: first wins, conflict recorded
   - Expected: d2.kind equals `command-conflict`
   - Expected: reg.count() equals `1`
   - Expected: reg.conflict_count() equals `1`
   - Expected: reg.owner_of("shared.cmd") equals `ext-a`
   - Expected: out equals `ran:p`
   - Expected: "first handler" equals `missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("duplicate command id: first wins, conflict recorded")
step("Verify: duplicate command id: first wins, conflict recorded")
val reg = CommandRegistry.new()
reg.register("ext-a", "shared.cmd", "First", registry_spec_ok_handler)
val d2 = reg.register("ext-b", "shared.cmd", "Second", registry_spec_other_handler)
expect(d2.kind).to_equal("command-conflict")
expect(reg.count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(reg.conflict_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(reg.owner_of("shared.cmd")).to_equal("ext-a")
match reg.run("shared.cmd", "p"):
    case Ok(out):
        expect(out).to_equal("ran:p")
    case Err(_):
        expect("first handler").to_equal("missing")
```

</details>

#### disposal removes the registration

- disposal removes the registration
- Verify: disposal removes the registration
   - Expected: reg.dispose(d.id) is true
   - Expected: reg.has("a.run") is false
   - Expected: "disposed" equals `still ran`
   - Expected: e contains `no handler registered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("disposal removes the registration")
step("Verify: disposal removes the registration")
val reg = CommandRegistry.new()
val d = reg.register("ext-a", "a.run", "Run", registry_spec_ok_handler)
expect(reg.dispose(d.id)).to_equal(true)
expect(reg.has("a.run")).to_equal(false)
match reg.run("a.run", "x"):
    case Ok(_):
        expect("disposed").to_equal("still ran")
    case Err(e):
        expect(e.contains("no handler registered")).to_equal(true)
```

</details>

#### dispose_owner removes all of one owner's registrations, keeps others

- dispose_owner removes all of one owner's registrations, keeps others
- Verify: dispose_owner removes all of one owner's registrations, keeps others
   - Expected: reg.dispose_owner("ext-a") equals `2`
   - Expected: reg.count() equals `1`
   - Expected: reg.has("b.one") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispose_owner removes all of one owner's registrations, keeps others")
step("Verify: dispose_owner removes all of one owner's registrations, keeps others")
val reg = CommandRegistry.new()
reg.register("ext-a", "a.one", "One", registry_spec_ok_handler)
reg.register("ext-a", "a.two", "Two", registry_spec_ok_handler)
reg.register("ext-b", "b.one", "BOne", registry_spec_other_handler)
expect(reg.dispose_owner("ext-a")).to_equal(2)
expect(reg.count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(reg.has("b.one")).to_equal(true)
```

</details>

#### command_ids preserves stable insertion order

- command_ids preserves stable insertion order
- Verify: command_ids preserves stable insertion order
   - Expected: ids.len() equals `2`
   - Expected: ids[0] equals `z.last`
   - Expected: ids[1] equals `a.first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("command_ids preserves stable insertion order")
step("Verify: command_ids preserves stable insertion order")
val reg = CommandRegistry.new()
reg.register("e", "z.last", "Z", registry_spec_ok_handler)
reg.register("e", "a.first", "A", registry_spec_ok_handler)
val ids = reg.command_ids()
expect(ids.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(ids[0]).to_equal("z.last")
expect(ids[1]).to_equal("a.first")
```

</details>

### EventListenerRegistry

#### delivers to matching listeners and counts them

- delivers to matching listeners and counts them
- Verify: delivers to matching listeners and counts them
   - Expected: reg.deliver("doc.saved", "p") equals `2`
   - Expected: reg.deliver("doc.opened", "p") equals `1`
   - Expected: reg.deliver("doc.closed", "p") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("delivers to matching listeners and counts them")
step("Verify: delivers to matching listeners and counts them")
val reg = EventListenerRegistry.new()
reg.add("ext-a", "doc.saved", registry_spec_listener)
reg.add("ext-b", "doc.saved", registry_spec_listener)
reg.add("ext-c", "doc.opened", registry_spec_listener)
expect(reg.deliver("doc.saved", "p")).to_equal(2)
expect(reg.deliver("doc.opened", "p")).to_equal(1)
expect(reg.deliver("doc.closed", "p")).to_equal(0)
```

</details>

#### disposal removes a listener

- disposal removes a listener
- Verify: disposal removes a listener
   - Expected: d.kind equals `listener`
   - Expected: reg.dispose(d.id) is true
   - Expected: reg.deliver("doc.saved", "p") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("disposal removes a listener")
step("Verify: disposal removes a listener")
val reg = EventListenerRegistry.new()
val d = reg.add("ext-a", "doc.saved", registry_spec_listener)
expect(d.kind).to_equal("listener")
expect(reg.dispose(d.id)).to_equal(true)
expect(reg.deliver("doc.saved", "p")).to_equal(0)
```

</details>

### LanguageIndex

#### maps file extensions to language ids and removes by owner

- maps file extensions to language ids and removes by owner
- Verify: maps file extensions to language ids and removes by owner
   - Expected: idx.language_for_file_ext(".md") equals `markdown`
   - Expected: idx.language_for_file_ext(".spl") equals `simple`
   - Expected: idx.language_for_file_ext(".xyz") equals ``
   - Expected: idx.remove_owner("md-ext") equals `1`
   - Expected: idx.language_for_file_ext(".md") equals ``
   - Expected: idx.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps file extensions to language ids and removes by owner")
step("Verify: maps file extensions to language ids and removes by owner")
val idx = LanguageIndex.new()
idx.register("md-ext", "markdown", [".md", ".markdown"])
idx.register("spl-ext", "simple", [".spl"])
expect(idx.language_for_file_ext(".md")).to_equal("markdown")
expect(idx.language_for_file_ext(".spl")).to_equal("simple")
expect(idx.language_for_file_ext(".xyz")).to_equal("")
expect(idx.remove_owner("md-ext")).to_equal(1)
expect(idx.language_for_file_ext(".md")).to_equal("")
expect(idx.count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
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

- Canonical SPipe generation for source `0735aea0dce9e007eefde3207ac74cedc61334964cd202a83a46675a7c327516`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0735aea0dce9e007eefde3207ac74cedc61334964cd202a83a46675a7c327516`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0735aea0dce9e007eefde3207ac74cedc61334964cd202a83a46675a7c327516`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/editor/extensions/registry_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/extensions/registry_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/extensions/registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/extensions/registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/extensions/registry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/editor/extensions/registry_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the registered typed handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/extensions/registry_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates handler errors as Err' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/extensions/registry_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'running an unregistered command fails cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
