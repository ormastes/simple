# access_cli_grammar_spec

> Purpose: Prove that Shared UI CLI access grammar.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# access_cli_grammar_spec

Purpose: Prove that Shared UI CLI access grammar.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/access_cli_grammar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Shared UI CLI access grammar.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Shared UI CLI access grammar

#### should recognize only the six shared operations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should recognize only the six shared operations
- Verify: should recognize only the six shared operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should recognize only the six shared operations")
step("Verify: should recognize only the six shared operations")
# @req: REQ-LIB-COMMON-001
expect(access_operation_is_valid(ACCESS_OPERATION_LIST)).to_be(true)
expect(access_operation_is_valid(ACCESS_OPERATION_SNAPSHOT)).to_be(true)
expect(access_operation_is_valid(ACCESS_OPERATION_SURFACE)).to_be(true)
expect(access_operation_is_valid(ACCESS_OPERATION_FIND)).to_be(true)
expect(access_operation_is_valid(ACCESS_OPERATION_ACT)).to_be(true)
expect(access_operation_is_valid(ACCESS_OPERATION_HISTORY)).to_be(true)
expect(access_operation_is_valid("cmm")).to_be(false)
```

</details>

#### should recognize human and JSON output modes

- should recognize human and JSON output modes
- Verify: should recognize human and JSON output modes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should recognize human and JSON output modes")
step("Verify: should recognize human and JSON output modes")
expect(access_output_mode_is_valid(ACCESS_OUTPUT_HUMAN)).to_be(true)
expect(access_output_mode_is_valid(ACCESS_OUTPUT_JSON)).to_be(true)
expect(access_output_mode_is_valid("xml")).to_be(false)
```

</details>

#### should resolve canonical names and compatibility aliases

- should resolve canonical names and compatibility aliases
- Verify: should resolve canonical names and compatibility aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should resolve canonical names and compatibility aliases")
step("Verify: should resolve canonical names and compatibility aliases")
val descriptors = [_read_descriptor(0)]
match access_find_descriptor("windows", "", descriptors):
    Some(found): expect(found.handler_key).to_equal("ui.windows")
    nil: fail("canonical descriptor was not found")
match access_find_descriptor("wm-list", "", descriptors):
    Some(found): expect(found.operation).to_equal(ACCESS_OPERATION_LIST)
    nil: fail("alias descriptor was not found")
expect(access_find_descriptor("missing", "", descriptors)).to_be_nil()
```

</details>

#### should reject missing positional arguments

- should reject missing positional arguments
- Verify: should reject missing positional arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject missing positional arguments")
step("Verify: should reject missing positional arguments")
val request = AccessRequest.create(_read_descriptor(1), ACCESS_OUTPUT_HUMAN, "simple_ui", "ui-1", "r1", [], 2000, false)
match access_validate_request(request):
    Err(e): expect(e.code).to_equal("invalid_argument")
    Ok(_): fail("missing arguments were accepted")
```

</details>

#### should reject invalid output and timeout values

- should reject invalid output and timeout values
- Verify: should reject invalid output and timeout values


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject invalid output and timeout values")
step("Verify: should reject invalid output and timeout values")
val bad_output = AccessRequest.create(_read_descriptor(0), "xml", "simple_ui", "", "r2", [], 2000, false)
match access_validate_request(bad_output):
    Err(e): expect(e.message).to_contain("output mode")
    Ok(_): fail("invalid output mode was accepted")
val bad_timeout = AccessRequest.create(_read_descriptor(0), ACCESS_OUTPUT_JSON, "simple_ui", "", "r3", [], 0, false)
match access_validate_request(bad_timeout):
    Err(e): expect(e.message).to_contain("timeout")
    Ok(_): fail("invalid timeout was accepted")
```

</details>

#### should require explicit confirmation only when policy requires it

- should require explicit confirmation only when policy requires it
- Verify: should require explicit confirmation only when policy requires it


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should require explicit confirmation only when policy requires it")
step("Verify: should require explicit confirmation only when policy requires it")
val blocked = AccessRequest.create(_act_descriptor(true), ACCESS_OUTPUT_JSON, "simple_ui", "", "r4", ["main#ok", "click"], 2000, false)
match access_validate_request(blocked):
    Err(e): expect(e.code).to_equal("interaction_required")
    Ok(_): fail("unconfirmed action was accepted")
val confirmed = AccessRequest.create(_act_descriptor(true), ACCESS_OUTPUT_JSON, "simple_ui", "", "r5", ["main#ok", "click"], 2000, true)
match access_validate_request(confirmed):
    Ok(_): expect(confirmed.confirmed).to_be(true)
    Err(e): fail("confirmed action was rejected: " + e.message)
```

</details>

#### should validate actions against current advertised target state

- should validate actions against current advertised target state
- Verify: should validate actions against current advertised target state


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should validate actions against current advertised target state")
step("Verify: should validate actions against current advertised target state")
val snapshot = _snapshot()
match access_validate_snapshot_action(snapshot, "a#root", "click"):
    Ok(node): expect(node.canonical_id).to_equal("a#root")
    Err(e): fail("advertised action was rejected: " + e.message)
match access_validate_snapshot_action(snapshot, "a#root", "type_text"):
    Err(e): expect(e.code).to_equal("unsupported_action")
    Ok(_): fail("unadvertised action was accepted")
match access_validate_snapshot_action(snapshot, "missing#root", "click"):
    Err(e): expect(e.code).to_equal("target_not_found")
    Ok(_): fail("missing target was accepted")
```

</details>

#### should normalize and sort window rows through one common projector

- should normalize and sort window rows through one common projector
- Verify: should normalize and sort window rows through one common projector
   - Expected: result.rows.len() equals `3`
   - Expected: result.rows[0] equals `["ID", "TITLE", "OWNER", "KIND", "STATE", "GEOMETRY", "FOCUS", "VISIBLE", "PA... (full value in folded executable source)`
   - Expected: result.rows[1][0] equals `a`
   - Expected: result.rows[1][10] equals `7`
   - Expected: result.rows[2][0] equals `z`
   - Expected: result.returned_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should normalize and sort window rows through one common projector")
step("Verify: should normalize and sort window rows through one common projector")
val result = access_result_from_snapshot(ACCESS_OPERATION_LIST, "simple_ui", "ui-1", _snapshot(), 10)
expect(result.rows.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(result.rows[0]).to_equal(["ID", "TITLE", "OWNER", "KIND", "STATE", "GEOMETRY", "FOCUS", "VISIBLE", "PARENT", "CAPS", "REVISION", "CAPTURED_AT", "GENERATION", "STALE"])
expect(result.rows[1][0]).to_equal("a")
expect(result.rows[1][10]).to_equal("7")
expect(result.rows[2][0]).to_equal("z")
expect(result.returned_count).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result.truncated).to_be(false)
```

</details>

#### should apply focused filtering before the bounded result limit

- should apply focused filtering before the bounded result limit
- Verify: should apply focused filtering before the bounded result limit
   - Expected: matches.len() equals `1`
   - Expected: matches[0].canonical_id equals `a#root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should apply focused filtering before the bounded result limit")
step("Verify: should apply focused filtering before the bounded result limit")
val matches = ui_access_find_nodes_filtered(_snapshot(), "", "", "", true, 1)
expect(matches.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(matches[0].canonical_id).to_equal("a#root")
expect(matches[0].focused).to_be(true)
```

</details>

#### should expose truncation and the same semantic result in both modes

- should expose truncation and the same semantic result in both modes
- Verify: should expose truncation and the same semantic result in both modes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose truncation and the same semantic result in both modes")
step("Verify: should expose truncation and the same semantic result in both modes")
val result = access_result_from_snapshot(ACCESS_OPERATION_LIST, "simple_ui", "ui-1", _snapshot(), 1)
expect(result.truncated).to_be(true)
expect(access_render_human(result)).to_contain("Alpha")
val json = access_render_json(result)
expect(json).to_contain("\"schema\":\"simple.access/v1\"")
expect(json).to_contain("\"operation\":\"list\"")
expect(json).to_contain("\"truncated\":true")
expect(json).to_contain("\"id\":\"a\"")
```

</details>

#### should reject malformed geometry and serialize duplicate props once

- should reject malformed geometry and serialize duplicate props once
- Verify: should reject malformed geometry and serialize duplicate props once
   - Expected: snapshot_json.split("\"x\":").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject malformed geometry and serialize duplicate props once")
step("Verify: should reject malformed geometry and serialize duplicate props once")
val root = UiAccessNode(canonical_id: "g#root", surface_id: "g", widget_id: "root", kind: "gui", visible: true, focused: false, enabled: true, selected: false, text_value: "Geometry", props: [UiAccessProp(key: "x", value: "bad"), UiAccessProp(key: "x", value: "9"), UiAccessProp(key: "y", value: "2"), UiAccessProp(key: "width", value: "3"), UiAccessProp(key: "height", value: "4")], child_ids: [], action_names: [])
val surface = UiAccessSurface(surface_id: "g", title: "Geometry", active: true, window_id: "", app_id: "fixture", root_canonical_id: "g#root")
val snapshot = UiAccessSnapshot(protocol_version: 1, snapshot_revision: 1, mode: "gui", active_surface: "g", surfaces: [surface], nodes: [root], recent_events: [])
val list_json = access_render_json(access_result_from_snapshot(ACCESS_OPERATION_LIST, "simple_ui", "", snapshot, 1))
expect(list_json).to_contain("\"geometry\":null")
val snapshot_json = ui_access_snapshot_to_json(snapshot)
expect(snapshot_json.split("\"x\":").len()).to_equal(2)
```

</details>

#### should preserve T32-compatible scalar table list and raw rendering

- should preserve T32-compatible scalar table list and raw rendering
- Verify: should preserve T32-compatible scalar table list and raw rendering
   - Expected: access_render_human(AccessResult.scalar_titled("State", "ready")) equals `State: ready`
   - Expected: access_render_human(AccessResult.raw("captured text")) equals `captured text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve T32-compatible scalar table list and raw rendering")
step("Verify: should preserve T32-compatible scalar table list and raw rendering")
expect(access_render_human(AccessResult.scalar_titled("State", "ready"))).to_equal("State: ready")
expect(access_render_human(AccessResult.table("Rows", [["A", "B"], ["1", "2"]]))).to_contain("1  2")
expect(access_render_human(AccessResult.list("Items", ["one"]))).to_contain("- one")
expect(access_render_human(AccessResult.raw("captured text"))).to_equal("captured text")
```

</details>

#### should render typed errors without contaminating the message

- should render typed errors without contaminating the message
- Verify: should render typed errors without contaminating the message


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should render typed errors without contaminating the message")
step("Verify: should render typed errors without contaminating the message")
val error = AccessError.detailed("stale_target", "target is stale", "T4030", "list again", true, false)
val json = access_error_to_json(ACCESS_OPERATION_ACT, "r6", error)
expect(json).to_contain("\"code\":\"stale_target\"")
expect(json).to_contain("\"source_code\":\"T4030\"")
expect(json).to_contain("\"retryable\":true")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `70baac85ad6e13ed5c5fe5c903c296c6c20ccd9c077c8561a4be87cc6f74f3d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70baac85ad6e13ed5c5fe5c903c296c6c20ccd9c077c8561a4be87cc6f74f3d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70baac85ad6e13ed5c5fe5c903c296c6c20ccd9c077c8561a4be87cc6f74f3d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/access_cli_grammar_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/access_cli_grammar_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/access_cli_grammar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/access_cli_grammar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recognize only the six shared operations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should recognize only the six shared operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recognize human and JSON output modes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should recognize human and JSON output modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve canonical names and compatibility aliases' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve canonical names and compatibility aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing positional arguments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid output and timeout values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/access_cli_grammar_spec.spl:112:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require explicit confirmation only when policy requires it' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
