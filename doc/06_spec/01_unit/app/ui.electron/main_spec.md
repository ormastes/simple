# Main Specification

> 1. Ok

<!-- sdn-diagram:id=main_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=main_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

main_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=main_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Main Specification

## Scenarios

### Electron Main Creation

#### creates successfully

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ElectronMain.new(1280, 720, "Dev Preview", 3333)
match result:
    Ok(app):
        expect(true).to_be_true()
    Err(e):
        expect(false).to_be_true()
```

</details>

#### reports the electron backend

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ElectronMain.new(1280, 720, "Dev Preview", 3333)
match result:
    Ok(app):
        expect(app.backend_name() == "electron").to_be_true()
        expect(app.shell_transport_name() == "electron-shell-stdout-json").to_be_true()
        expect(app.shell_window_id() == "electron-main").to_be_true()
    Err(e):
        expect(false).to_be_true()
```

</details>

### Electron Main Compositor Wire-up

#### wires the compositor backend on start

1. Ok
2. Ok
3. app stop
4. Err
5. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ElectronMain.new(320, 240, "wm_compare", 3333)
match result:
    Ok(app):
        val started = app.start()
        match started:
            Ok(wired):
                expect(wired).to_be_true()
                expect(app.compositor_wired).to_be_true()
                expect(app.is_running()).to_be_true()
                app.stop()
            Err(e):
                expect(false).to_be_true()
    Err(e):
        expect(false).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.electron/main_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Electron Main Creation
- Electron Main Compositor Wire-up

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
