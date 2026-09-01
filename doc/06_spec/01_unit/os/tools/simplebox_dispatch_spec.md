# simplebox_dispatch_spec

> Purpose: dispatches echo via full path basename

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simplebox_dispatch_spec

Purpose: dispatches echo via full path basename

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tools/simplebox_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: dispatches echo via full path basename
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### simplebox multi-call dispatcher

### simplebox_dispatch by argv[0] basename

#### dispatches echo via full path basename

- dispatches echo via full path basename
- Verify: dispatches echo via full path basename
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches echo via full path basename")
step("Verify: dispatches echo via full path basename")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["/usr/bin/echo", "hello"])
expect(result).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### dispatches true via bare name

- dispatches true via bare name
- Verify: dispatches true via bare name
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches true via bare name")
step("Verify: dispatches true via bare name")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["true"])
expect(result).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### dispatches false via bare name

- dispatches false via bare name
- Verify: dispatches false via bare name
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches false via bare name")
step("Verify: dispatches false via bare name")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["false"])
expect(result).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### dispatches pwd via bare name

- dispatches pwd via bare name
- Verify: dispatches pwd via bare name
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches pwd via bare name")
step("Verify: dispatches pwd via bare name")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["pwd"])
expect(result).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

### simplebox_dispatch via simplebox/busybox argv[1]

#### dispatches echo via simplebox

- dispatches echo via simplebox
- Verify: dispatches echo via simplebox
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches echo via simplebox")
step("Verify: dispatches echo via simplebox")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["simplebox", "echo", "hello"])
expect(result).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### dispatches false via simplebox

- dispatches false via simplebox
- Verify: dispatches false via simplebox
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches false via simplebox")
step("Verify: dispatches false via simplebox")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["simplebox", "false"])
expect(result).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### dispatches true via busybox

- dispatches true via busybox
- Verify: dispatches true via busybox
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches true via busybox")
step("Verify: dispatches true via busybox")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["busybox", "true"])
expect(result).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### dispatches false via busybox

- dispatches false via busybox
- Verify: dispatches false via busybox
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches false via busybox")
step("Verify: dispatches false via busybox")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["/bin/busybox", "false"])
expect(result).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

### simplebox_dispatch edge cases

#### returns 127 for unknown applet via basename

- returns 127 for unknown applet via basename
- Verify: returns 127 for unknown applet via basename
   - Expected: result equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 127 for unknown applet via basename")
step("Verify: returns 127 for unknown applet via basename")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["unknowncmd"])
expect(result).to_equal(127)  # oracle: value fixed by the spec contract
```

</details>

#### returns 127 for unknown applet via simplebox

- returns 127 for unknown applet via simplebox
- Verify: returns 127 for unknown applet via simplebox
   - Expected: result equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 127 for unknown applet via simplebox")
step("Verify: returns 127 for unknown applet via simplebox")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["simplebox", "unknowncmd"])
expect(result).to_equal(127)  # oracle: value fixed by the spec contract
```

</details>

#### returns 0 for --list via simplebox

- returns 0 for --list via simplebox
- Verify: returns 0 for --list via simplebox
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for --list via simplebox")
step("Verify: returns 0 for --list via simplebox")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["simplebox", "--list"])
expect(result).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### returns 0 for --list as basename

- returns 0 for --list as basename
- Verify: returns 0 for --list as basename
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for --list as basename")
step("Verify: returns 0 for --list as basename")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["--list"])
expect(result).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### returns 127 for empty argv

- returns 127 for empty argv
- Verify: returns 127 for empty argv
   - Expected: result equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 127 for empty argv")
step("Verify: returns 127 for empty argv")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch([])
expect(result).to_equal(127)  # oracle: value fixed by the spec contract
```

</details>

#### returns 127 for simplebox with no applet argv

- returns 127 for simplebox with no applet argv
- Verify: returns 127 for simplebox with no applet argv
   - Expected: result equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 127 for simplebox with no applet argv")
step("Verify: returns 127 for simplebox with no applet argv")
# @req: REQ-OS-SimpDisp-001
val result = simplebox_dispatch(["simplebox"])
expect(result).to_equal(127)  # oracle: value fixed by the spec contract
```

</details>

### simplebox_has_applet

#### returns true for echo

- returns true for echo
- Verify: returns true for echo
   - Expected: simplebox_has_applet("echo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for echo")
step("Verify: returns true for echo")
# @req: REQ-OS-SimpDisp-001
expect(simplebox_has_applet("echo")).to_equal(true)
```

</details>

#### returns true for true

- returns true for true
- Verify: returns true for true
   - Expected: simplebox_has_applet("true") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for true")
step("Verify: returns true for true")
# @req: REQ-OS-SimpDisp-001
expect(simplebox_has_applet("true")).to_equal(true)
```

</details>

#### returns true for false

- returns true for false
- Verify: returns true for false
   - Expected: simplebox_has_applet("false") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for false")
step("Verify: returns true for false")
# @req: REQ-OS-SimpDisp-001
expect(simplebox_has_applet("false")).to_equal(true)
```

</details>

#### returns true for pwd

- returns true for pwd
- Verify: returns true for pwd
   - Expected: simplebox_has_applet("pwd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for pwd")
step("Verify: returns true for pwd")
# @req: REQ-OS-SimpDisp-001
expect(simplebox_has_applet("pwd")).to_equal(true)
```

</details>

#### returns true for filesystem applets

- returns true for filesystem applets
   - Expected: simplebox_has_applet("cat") is true
   - Expected: simplebox_has_applet("head") is true
   - Expected: simplebox_has_applet("wc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for filesystem applets")
expect(simplebox_has_applet("cat")).to_equal(true)
expect(simplebox_has_applet("head")).to_equal(true)
expect(simplebox_has_applet("wc")).to_equal(true)
```

</details>

#### returns true for the libc-backed seq applet

- returns true for the libc-backed seq applet
   - Expected: simplebox_has_applet("seq") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for the libc-backed seq applet")
expect(simplebox_has_applet("seq")).to_equal(true)
```

</details>

#### returns false for unknown

- returns false for unknown
- Verify: returns false for unknown
   - Expected: simplebox_has_applet("unknowncmd") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unknown")
step("Verify: returns false for unknown")
# @req: REQ-OS-SimpDisp-001
expect(simplebox_has_applet("unknowncmd")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: simplebox_has_applet("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for empty string")
step("Verify: returns false for empty string")
# @req: REQ-OS-SimpDisp-001
expect(simplebox_has_applet("")).to_equal(false)
```

</details>

### simplebox_applet_names

#### returns exactly 8 applets

- returns exactly 8 applets
- Verify: returns exactly 8 applets
   - Expected: names.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exactly 8 applets")
step("Verify: returns exactly 8 applets")
# @req: REQ-OS-SimpDisp-001
val names = simplebox_applet_names()
expect(names.len()).to_equal(8)  # oracle: value fixed by the spec contract
```

</details>

#### first applet is echo

- first applet is echo
- Verify: first applet is echo
   - Expected: names[0] equals `echo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first applet is echo")
step("Verify: first applet is echo")
# @req: REQ-OS-SimpDisp-001
val names = simplebox_applet_names()
expect(names[0]).to_equal("echo")
```

</details>

#### second applet is true

- second applet is true
- Verify: second applet is true
   - Expected: names[1] equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second applet is true")
step("Verify: second applet is true")
# @req: REQ-OS-SimpDisp-001
val names = simplebox_applet_names()
expect(names[1]).to_equal("true")
```

</details>

#### third applet is false

- third applet is false
- Verify: third applet is false
   - Expected: names[2] equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("third applet is false")
step("Verify: third applet is false")
# @req: REQ-OS-SimpDisp-001
val names = simplebox_applet_names()
expect(names[2]).to_equal("false")
```

</details>

#### fourth applet is pwd

- fourth applet is pwd
- Verify: fourth applet is pwd
   - Expected: names[3] equals `pwd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fourth applet is pwd")
step("Verify: fourth applet is pwd")
# @req: REQ-OS-SimpDisp-001
val names = simplebox_applet_names()
expect(names[3]).to_equal("pwd")
```

</details>

#### includes filesystem applets in stable order

- includes filesystem applets in stable order
   - Expected: names[4] equals `seq`
   - Expected: names[5] equals `cat`
   - Expected: names[6] equals `head`
   - Expected: names[7] equals `wc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes filesystem applets in stable order")
val names = simplebox_applet_names()
expect(names[4]).to_equal("seq")
expect(names[5]).to_equal("cat")
expect(names[6]).to_equal("head")
expect(names[7]).to_equal("wc")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-SimpDisp-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `16b0105a66dc66f15ef67420dd7034a45833927305a27f31d32b8772e63d1e52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16b0105a66dc66f15ef67420dd7034a45833927305a27f31d32b8772e63d1e52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16b0105a66dc66f15ef67420dd7034a45833927305a27f31d32b8772e63d1e52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/tools/simplebox_dispatch_spec.spl
mirror: doc/06_spec/01_unit/os/tools/simplebox_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tools/simplebox_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tools/simplebox_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tools/simplebox_dispatch_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches echo via full path basename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/simplebox_dispatch_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches true via bare name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/simplebox_dispatch_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches false via bare name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
