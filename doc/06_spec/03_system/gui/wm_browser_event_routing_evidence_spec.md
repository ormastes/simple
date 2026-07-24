# Wm Browser Event Routing Evidence Specification

> **Current result: BLOCKED.** The fail-closed wrapper contract was checked
> directly, but this SSpec has not run on a qualifying pure-Simple binary.
>
> <details>

<!-- sdn-diagram:id=wm_browser_event_routing_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_browser_event_routing_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_browser_event_routing_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_browser_event_routing_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 0 | 0 | 1 |

<details>
<summary>Full Scenario Manual</summary>

## Scenario

### WM browser event routing evidence

#### fails closed when a valid Simple run ID has no composition receipt

<details>
<summary>Executable SSpec</summary>

```simple
step("Provide a valid caller-supplied Simple run ID")
val run_id = _run_id()
val result = _run_checker(run_id)

step("Reject the missing authoritative composition receipt before Electron")
expect(result[2]).to_be_greater_than(0)
expect(result[0]).to_contain("wm_browser_event_routing_status=fail")
expect(result[0]).to_contain("wm_browser_event_routing_reason=missing-simple-web-font-composition-receipt")

val report = file_read_text(_report_path(run_id)) ?? ""
expect(report).to_contain("- status: fail")
expect(report).to_contain("- reason: missing-simple-web-font-composition-receipt")
```

</details>

## Ownership boundary

This spec covers only wrapper admission: a syntactically valid
`SIMPLE_WEB_FONT_RUN_ID` with no composition receipt must exit nonzero with
`missing-simple-web-font-composition-receipt`, before Electron launches.

Positive correlated browser focus, keyboard, pointer, timing, and frame
coverage is owned by
`test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | BLOCKED |
| Source | `test/03_system/gui/wm_browser_event_routing_evidence_spec.spl` |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 0 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 1 |

</details>
