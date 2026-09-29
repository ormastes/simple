# Vscode Extension Gen Specification

> Tests covering vscode manifest generation: deterministic, conformant, non-destructive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vscode Extension Gen Specification

## Scenarios

### vscode manifest generation: deterministic, conformant, non-destructive

#### generating twice produces byte-identical output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generating twice produces byte-identical output
   - Expected: first equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generating twice produces byte-identical output")
val first = vscode_manifest_generate()
val second = vscode_manifest_generate()
expect(first).to_equal(second)
expect(first.len()).to_be_greater_than(0)
```

</details>

#### the union command list is stable across repeated calls

- the union command list is stable across repeated calls
   - Expected: a.len() equals `b.len()`
   - Expected: all_match is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the union command list is stable across repeated calls")
val a = vscode_manifest_union_commands()
val b = vscode_manifest_union_commands()
expect(a.len()).to_equal(b.len())
var i = 0
var all_match = true
while i < a.len():
    if a[i].id != b[i].id:
        all_match = false
    i = i + 1
expect(all_match).to_equal(true)
```

</details>

#### the union command list is sorted by id

- the union command list is sorted by id
   - Expected: sorted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the union command list is sorted by id")
val commands = vscode_manifest_union_commands()
var sorted = true
var i = 1
while i < commands.len():
    if commands[i - 1].id > commands[i].id:
        sorted = false
    i = i + 1
expect(sorted).to_equal(true)
```

</details>

#### the generated package.json is already applied on disk (sync check passes)

- the generated package.json is already applied on disk (sync check passes)
   - Expected: vscode_manifest_sync_check() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the generated package.json is already applied on disk (sync check passes)")
expect(vscode_manifest_sync_check()).to_equal(true)
```

</details>

#### the checker reports zero HARD mismatches against the landed package.json

- the checker reports zero HARD mismatches against the landed package.json
   - Expected: hard.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the checker reports zero HARD mismatches against the landed package.json")
val hard = vscode_manifest_hard_mismatches()
expect(hard.len()).to_equal(0)
```

</details>

#### bridge-only vscode commands (no builtin owner) are preserved, not mismatches

- bridge-only vscode commands (no builtin owner) are preserved, not mismatches
   - Expected: bridge_only_count equals `mismatches.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bridge-only vscode commands (no builtin owner) are preserved, not mismatches")
val mismatches = vscode_manifest_check()
var bridge_only_count = 0
for m in mismatches:
    if m.starts_with("bridge-only: "):
        bridge_only_count = bridge_only_count + 1
expect(bridge_only_count).to_be_greater_than(0)
expect(bridge_only_count).to_equal(mismatches.len())
```

</details>

#### a known bridge-only command (simple.lsp.restart) survives generation with its original title

- a known bridge-only command (simple.lsp.restart) survives generation with its original title
   - Expected: found_title equals `Restart Simple LSP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a known bridge-only command (simple.lsp.restart) survives generation with its original title")
val generated = vscode_manifest_generate()
val parsed = json_parse(generated)
val commands = json_path_get(parsed, "contributes.commands")
val n = json_array_length(commands)
var found_title = ""
var i = 0
while i < n:
    val entry = json_array_get(commands, i)
    if _entry_text(entry, "command") == "simple.lsp.restart":
        found_title = _entry_text(entry, "title")
    i = i + 1
expect(found_title).to_equal("Restart Simple LSP")
```

</details>

#### a builtin command that was previously missing (simple.build) is now present

- a builtin command that was previously missing (simple.build) is now present
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a builtin command that was previously missing (simple.build) is now present")
val generated = vscode_manifest_generate()
val parsed = json_parse(generated)
val commands = json_path_get(parsed, "contributes.commands")
val n = json_array_length(commands)
var found = false
var i = 0
while i < n:
    val entry = json_array_get(commands, i)
    if _entry_text(entry, "command") == "simple.build":
        found = true
    i = i + 1
expect(found).to_equal(true)
```

</details>

#### the generated package.json stays parseable JSON with a non-empty commands array

- the generated package.json stays parseable JSON with a non-empty commands array
   - Expected: parsed == nil is false
   - Expected: json_is_array(commands) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the generated package.json stays parseable JSON with a non-empty commands array")
val generated = vscode_manifest_generate()
val parsed = json_parse(generated)
expect(parsed == nil).to_equal(false)
val commands = json_path_get(parsed, "contributes.commands")
expect(json_is_array(commands)).to_equal(true)
expect(json_array_length(commands)).to_be_greater_than(0)
```

</details>

#### on-disk package.json (read fresh) is itself valid JSON

- on-disk package.json (read fresh) is itself valid JSON
   - Expected: parsed == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("on-disk package.json (read fresh) is itself valid JSON")
val on_disk = file_read(vscode_package_json_path())
val parsed = json_parse(on_disk)
expect(parsed == nil).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/vscode_extension_gen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering vscode manifest generation: deterministic, conformant, non-destructive.
- vscode manifest generation: deterministic, conformant, non-destructive

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `798ea3db647fe05ad0508644bbc555a957d692847cba6e16a821f2a5d833065b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `798ea3db647fe05ad0508644bbc555a957d692847cba6e16a821f2a5d833065b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `798ea3db647fe05ad0508644bbc555a957d692847cba6e16a821f2a5d833065b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/vscode_extension_gen_spec.spl
mirror: doc/06_spec/01_unit/app/vscode_extension_gen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/vscode_extension_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/vscode_extension_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/vscode_extension_gen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/vscode_extension_gen_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generating twice produces byte-identical output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/vscode_extension_gen_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the union command list is stable across repeated calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/vscode_extension_gen_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the union command list is sorted by id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
