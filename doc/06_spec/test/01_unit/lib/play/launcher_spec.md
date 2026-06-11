# launcher_spec

> Validates the Electron launcher helpers: ws URL parsing, arg building, and executable resolution. Tests only the pure functions — no real process spawning.

<!-- sdn-diagram:id=launcher_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=launcher_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

launcher_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=launcher_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# launcher_spec

Validates the Electron launcher helpers: ws URL parsing, arg building, and executable resolution. Tests only the pure functions — no real process spawning.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PLAY-002 |
| Category | Stdlib \| Play |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/play/launcher_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Validates the Electron launcher helpers: ws URL parsing, arg building,
and executable resolution. Tests only the pure functions — no real
process spawning.

## Scenarios

### extract_ws_url_from_text

#### extracts ws URL from typical Electron stderr

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = "some startup noise\nDevTools listening on ws://127.0.0.1:9222/devtools/browser/abc\nmore stuff"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("ws://127.0.0.1:9222/devtools/browser/abc")
```

</details>

#### returns empty for log without marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = "no devtools marker here\nstill nothing"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("")
```

</details>

#### handles URL at end of string without trailing newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = "DevTools listening on ws://localhost:12345/devtools"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("ws://localhost:12345/devtools")
```

</details>

#### stops at newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = "DevTools listening on ws://host:1/p\nmore"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("ws://host:1/p")
```

</details>

#### stops at space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = "DevTools listening on ws://host:1/path (metadata)"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("ws://host:1/path")
```

</details>

### launcher_build_args

#### appends debugging port when not present

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = launcher_build_args([".", "--no-sandbox"], 0)
var found = false
for a in args:
    if a.contains("--remote-debugging-port"):
        found = true
expect(found).to_equal(true)
```

</details>

#### does not duplicate debugging port if already present

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = launcher_build_args([".", "--remote-debugging-port=9222"], 0)
var count = 0
for a in args:
    if a.contains("--remote-debugging-port"):
        count = count + 1
expect(count).to_equal(1)
```

</details>

#### preserves existing args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = launcher_build_args([".", "--no-sandbox"], 0)
expect(args[0]).to_equal(".")
expect(args[1]).to_equal("--no-sandbox")
```

</details>

### launcher_resolve_executable

#### uses executable_path when set

1. var opts = default launch options
   - Expected: cmd equals `/usr/bin/electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = default_launch_options()
opts.executable_path = "/usr/bin/electron"
val (cmd, args) = launcher_resolve_executable(opts)
expect(cmd).to_equal("/usr/bin/electron")
```

</details>

#### falls back to npx electron with no args

1. var opts = default launch options
   - Expected: cmd equals `npx`
   - Expected: args[0] equals `electron`
   - Expected: args[1] equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = default_launch_options()
val (cmd, args) = launcher_resolve_executable(opts)
expect(cmd).to_equal("npx")
expect(args[0]).to_equal("electron")
expect(args[1]).to_equal(".")
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
