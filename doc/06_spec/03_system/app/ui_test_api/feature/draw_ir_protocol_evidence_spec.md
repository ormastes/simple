# Draw IR Protocol Evidence

> Captures real UI test API Draw IR Protocol-v2 layout and diff responses through `handle_test_request`.

<!-- sdn-diagram:id=draw_ir_protocol_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_protocol_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_protocol_evidence_spec -> std
draw_ir_protocol_evidence_spec -> app
draw_ir_protocol_evidence_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_ir_protocol_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw IR Protocol Evidence

Captures real UI test API Draw IR Protocol-v2 layout and diff responses through `handle_test_request`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/03_plan/sys_test/draw_ir_protocol_evidence.md |
| Plan | doc/03_plan/sys_test/draw_ir_protocol_evidence.md |
| Design | doc/05_design/app/ui_test_api/draw_ir_protocol_evidence.md |
| Source | `test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl` |
| Updated | 2026-06-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Captures real UI test API Draw IR Protocol-v2 layout and diff responses through
`handle_test_request`.

**Requirements:** doc/03_plan/sys_test/draw_ir_protocol_evidence.md
**Plan:** doc/03_plan/sys_test/draw_ir_protocol_evidence.md
**Design:** doc/05_design/app/ui_test_api/draw_ir_protocol_evidence.md
**Artifacts:** build/test-artifacts/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence/draw_ir_protocol.json

## Syntax

The spec calls the UI test API handler directly and writes the protocol output
that a test client would inspect.

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `draw_ir_protocol.json` | JSON artifact | `build/test-artifacts/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence/draw_ir_protocol.json` |

## Scenarios

### Draw IR protocol evidence

#### captures layout geometry and baseline diff protocol output

1.  protocol record

2.  protocol record

3.  protocol record
   - Expected: _write_capture(capture) equals `0`
   - Expected: _capture_file_state(capture) equals `matched`


<details>
<summary>Executable SPipe</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = _make_state()
val (layout_status, layout_ctype, layout_body) = handle_test_request(
    "/api/test/draw-ir/layout?id=root&capability=draw_ir",
    "GET",
    "",
    state,
    _noop_inject,
    nil
)
val (current_status, current_ctype, current_body) = handle_test_request(
    "/api/test/draw-ir/diff?baseline=current&capability=draw_ir",
    "GET",
    "",
    state,
    _noop_inject,
    nil
)
val (empty_status, empty_ctype, empty_body) = handle_test_request(
    "/api/test/draw-ir/diff?baseline=empty&capability=draw_ir",
    "GET",
    "",
    state,
    _noop_inject,
    nil
)

expect(layout_status).to_equal(200)
expect(layout_ctype).to_equal("application/vnd.simple.draw-ir+json")
expect(layout_body).to_contain("\"id\":\"root\"")
expect(layout_body).to_contain("\"geometry\"")
expect(layout_body).to_contain("\"hit_rect\"")
expect(layout_body).to_contain("\"computed_style\"")
expect(current_status).to_equal(200)
expect(current_body).to_contain("\"mode\":\"baseline\"")
expect(current_body).to_contain("\"changed_count\":0")
expect(empty_status).to_equal(200)
expect(empty_body).to_contain("\"state\":\"added\"")

val capture = "[\n" +
    _protocol_record("layout", layout_status, layout_ctype, layout_body) + ",\n" +
    _protocol_record("baseline_current", current_status, current_ctype, current_body) + ",\n" +
    _protocol_record("baseline_empty", empty_status, empty_ctype, empty_body) + "\n]"
expect(_write_capture(capture)).to_equal(0)
expect(_capture_file_state(capture)).to_equal("matched")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/sys_test/draw_ir_protocol_evidence.md](doc/03_plan/sys_test/draw_ir_protocol_evidence.md)
- **Plan:** [doc/03_plan/sys_test/draw_ir_protocol_evidence.md](doc/03_plan/sys_test/draw_ir_protocol_evidence.md)
- **Design:** [doc/05_design/app/ui_test_api/draw_ir_protocol_evidence.md](doc/05_design/app/ui_test_api/draw_ir_protocol_evidence.md)


</details>
