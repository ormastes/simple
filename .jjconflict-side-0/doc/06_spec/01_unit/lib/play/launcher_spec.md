# Launcher Specification

> Tests covering extract_ws_url_from_text, launcher_build_args, launcher_resolve_executable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Launcher Specification

## Scenarios

### extract_ws_url_from_text

#### extracts ws URL from typical Electron stderr

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts ws URL from typical Electron stderr
   - Expected: url equals `ws://127.0.0.1:9222/devtools/browser/abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts ws URL from typical Electron stderr")
val log = "some startup noise\nDevTools listening on ws://127.0.0.1:9222/devtools/browser/abc\nmore stuff"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("ws://127.0.0.1:9222/devtools/browser/abc")
```

</details>

#### returns empty for log without marker

- returns empty for log without marker
   - Expected: url equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty for log without marker")
val log = "no devtools marker here\nstill nothing"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("")
```

</details>

#### handles URL at end of string without trailing newline

- handles URL at end of string without trailing newline
   - Expected: url equals `ws://localhost:12345/devtools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles URL at end of string without trailing newline")
val log = "DevTools listening on ws://localhost:12345/devtools"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("ws://localhost:12345/devtools")
```

</details>

#### stops at newline

- stops at newline
   - Expected: url equals `ws://host:1/p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stops at newline")
val log = "DevTools listening on ws://host:1/p\nmore"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("ws://host:1/p")
```

</details>

#### stops at space

- stops at space
   - Expected: url equals `ws://host:1/path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stops at space")
val log = "DevTools listening on ws://host:1/path (metadata)"
val url = extract_ws_url_from_text(log)
expect(url).to_equal("ws://host:1/path")
```

</details>

### launcher_build_args

#### appends debugging port when not present

- appends debugging port when not present
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("appends debugging port when not present")
val args = launcher_build_args([".", "--no-sandbox"], 0)
var found = false
for a in args:
    if a.contains("--remote-debugging-port"):
        found = true
expect(found).to_equal(true)
```

</details>

#### does not duplicate debugging port if already present

- does not duplicate debugging port if already present
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not duplicate debugging port if already present")
val args = launcher_build_args([".", "--remote-debugging-port=9222"], 0)
var count = 0
for a in args:
    if a.contains("--remote-debugging-port"):
        count = count + 1
expect(count).to_equal(1)
```

</details>

#### preserves existing args

- preserves existing args
   - Expected: args[0] equals `.`
   - Expected: args[1] equals `--no-sandbox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves existing args")
val args = launcher_build_args([".", "--no-sandbox"], 0)
expect(args[0]).to_equal(".")
expect(args[1]).to_equal("--no-sandbox")
```

</details>

### launcher_resolve_executable

#### uses executable_path when set

- uses executable_path when set
   - Expected: cmd equals `/usr/bin/electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses executable_path when set")
var opts = default_launch_options()
opts.executable_path = "/usr/bin/electron"
val (cmd, args) = launcher_resolve_executable(opts)
expect(cmd).to_equal("/usr/bin/electron")
```

</details>

#### falls back to npx electron with no args

- falls back to npx electron with no args
   - Expected: cmd equals `npx`
   - Expected: args[0] equals `electron`
   - Expected: args[1] equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to npx electron with no args")
var opts = default_launch_options()
val (cmd, args) = launcher_resolve_executable(opts)
expect(cmd).to_equal("npx")
expect(args[0]).to_equal("electron")
expect(args[1]).to_equal(".")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/play/launcher_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering extract_ws_url_from_text, launcher_build_args, launcher_resolve_executable.
- extract_ws_url_from_text
- launcher_build_args
- launcher_resolve_executable

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e595c4e04cf407b9dfd0ff6a987cb707d6f5357619b99a9303ec6ad76442bdb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e595c4e04cf407b9dfd0ff6a987cb707d6f5357619b99a9303ec6ad76442bdb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e595c4e04cf407b9dfd0ff6a987cb707d6f5357619b99a9303ec6ad76442bdb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/play/launcher_spec.spl
mirror: doc/06_spec/01_unit/lib/play/launcher_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/play/launcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/play/launcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/play/launcher_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/play/launcher_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts ws URL from typical Electron stderr' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/play/launcher_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty for log without marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/play/launcher_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles URL at end of string without trailing newline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
