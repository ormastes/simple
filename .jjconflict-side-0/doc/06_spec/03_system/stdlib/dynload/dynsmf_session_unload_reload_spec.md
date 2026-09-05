# dynSMF Session Unload Reload System Specification

> Verifies the selected low_dependency_ui_dynsmf dynSMF lifecycle at the system boundary. The spec covers default stdlib-like autoload, per-id opt-out, and the interpreter-testable unload/stale/reload behavior needed for every selected stdlib-like dynSMF library to test itself without retaining stale session state.

<!-- sdn-diagram:id=dynsmf_session_unload_reload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynsmf_session_unload_reload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynsmf_session_unload_reload_spec -> std
dynsmf_session_unload_reload_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynsmf_session_unload_reload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dynSMF Session Unload Reload System Specification

Verifies the selected low_dependency_ui_dynsmf dynSMF lifecycle at the system boundary. The spec covers default stdlib-like autoload, per-id opt-out, and the interpreter-testable unload/stale/reload behavior needed for every selected stdlib-like dynSMF library to test itself without retaining stale session state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the selected low_dependency_ui_dynsmf dynSMF lifecycle at the system
boundary. The spec covers default stdlib-like autoload, per-id opt-out, and the
interpreter-testable unload/stale/reload behavior needed for every selected
stdlib-like dynSMF library to test itself without retaining stale session state.

## Examples

Default startup autoloads all six selected stdlib-like precompiled SMF
libraries through the SMF dynlib facade after validating the generated
`build/dynsmf/*.smf` artifacts. A per-id disable policy skips only the named
entries. Unloading any selected default library makes symbol lookup stale until
autoload reloads it with a newer generation.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Traceability:** REQ-004, REQ-005, REQ-006, REQ-007, REQ-008, REQ-009, REQ-010, NFR-003, NFR-005, NFR-006
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### low dependency UI dynSMF session lifecycle

#### autoloads the six selected stdlib-like precompiled SMF libraries by default

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val plans = dynsmf_build_plans(manifest)
expect(manifest.len()).to_equal(6)
expect(dynsmf_build_plans_ready(plans)).to_equal(true)
expect(dynsmf_artifacts_ready(manifest)).to_equal(true)

val session = dynsmf_session_autoload_checked(dynsmf_session_new("system-default", dynsmf_policy_default()), manifest)
expect(session.loaded.len()).to_equal(6)
expect(session.loaded[0].id).to_equal("file_io")
expect(session.loaded[5].id).to_equal("tui_renderer")
expect(session.evidence[0].reason).to_equal("smf_dlopen")
```

</details>

#### honors per-library dynSMF disable policy while loading other defaults

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val policy = dynsmf_policy_from_args_env(["--disable-dynsmf=web_renderer,tui_renderer"], "", "")
val session = dynsmf_session_autoload(dynsmf_session_new("system-disable", policy), manifest)
expect(session.loaded.len()).to_equal(4)
expect(session.evidence[3].library_id).to_equal("web_renderer")
expect(session.evidence[3].action).to_equal("skip")
expect(session.evidence[5].library_id).to_equal("tui_renderer")
expect(session.evidence[5].action).to_equal("skip")
```

</details>

#### unloads records stale symbol evidence and reloads with a newer generation

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val loaded = dynsmf_session_autoload(dynsmf_session_new("system-reload", dynsmf_policy_default()), manifest)
val before = dynsmf_session_symbol(loaded, "tui_renderer", "render_tui_tree")
expect(before.status).to_equal("ok")

val unloaded = dynsmf_session_unload(loaded, "tui_renderer")
val with_stale = dynsmf_session_record_symbol(unloaded, "tui_renderer", "render_tui_tree")
expect(with_stale.evidence[7].action).to_equal("symbol")
expect(with_stale.evidence[7].status).to_equal("stale")
expect(with_stale.evidence[7].reason).to_equal("unloaded")

val reloaded = dynsmf_session_autoload(with_stale, manifest)
val after = dynsmf_session_symbol(reloaded, "tui_renderer", "render_tui_tree")
expect(after.status).to_equal("ok")
expect(after.generation).to_be_greater_than(before.generation)
expect(reloaded.evidence[8].action).to_equal("reload")
```

</details>

#### unloads and reloads every selected default dynSMF library

1. var session = dynsmf session autoload checked
   - Expected: before.status equals `ok`
   - Expected: stale.status equals `stale`
   - Expected: stale.reason equals `unloaded`
   - Expected: after.status equals `ok`


<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
var session = dynsmf_session_autoload_checked(dynsmf_session_new("system-all-reload", dynsmf_policy_default()), manifest)
val ids = ["file_io", "net_io", "render2d", "web_renderer", "gui_renderer", "tui_renderer"]
val symbols = ["open", "connect", "draw", "render_html", "render_gui", "render_tui_tree"]

var idx = 0
while idx < ids.len():
    val id = ids[idx]
    val symbol = symbols[idx]
    val before = dynsmf_session_symbol(session, id, symbol)
    expect(before.status).to_equal("ok")

    val unloaded = dynsmf_session_unload(session, id)
    val stale = dynsmf_session_symbol(unloaded, id, symbol)
    expect(stale.status).to_equal("stale")
    expect(stale.reason).to_equal("unloaded")

    val reloaded = dynsmf_session_autoload_checked(unloaded, manifest)
    val after = dynsmf_session_symbol(reloaded, id, symbol)
    expect(after.status).to_equal("ok")
    expect(after.generation).to_be_greater_than(before.generation)
    session = reloaded
    idx = idx + 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/low_dependency_ui_dynsmf.md](doc/02_requirements/nfr/low_dependency_ui_dynsmf.md)
- **Plan:** [doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md](doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md)
- **Design:** [doc/05_design/low_dependency_ui_dynsmf.md](doc/05_design/low_dependency_ui_dynsmf.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>
