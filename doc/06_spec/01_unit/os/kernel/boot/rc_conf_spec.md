# rc.conf Screen Configuration Keys

> As an operator I want to pick which screen SimpleOS boots into by writing a single `screen_type` line in `/etc/rc.conf`, and I want a typo or a missing file to leave me with today's working window manager rather than a black screen. These scenarios exercise the pure normalization layer of the rc.conf reader, so they run without a mounted VFS while covering exactly the value handling the boot path depends on.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rc.conf Screen Configuration Keys

As an operator I want to pick which screen SimpleOS boots into by writing a single `screen_type` line in `/etc/rc.conf`, and I want a typo or a missing file to leave me with today's working window manager rather than a black screen. These scenarios exercise the pure normalization layer of the rc.conf reader, so they run without a mounted VFS while covering exactly the value handling the boot path depends on.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | simpleos-config-screen-selection |
| Category | OS / Boot / Configuration |
| Status | In Progress |
| Plan | doc/03_plan/os/simpleos/screens/ws_a_config_screen_selection_detail.md |
| Source | `test/01_unit/os/kernel/boot/rc_conf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

As an operator I want to pick which screen SimpleOS boots into by writing a
single `screen_type` line in `/etc/rc.conf`, and I want a typo or a missing
file to leave me with today's working window manager rather than a black
screen. These scenarios exercise the pure normalization layer of the rc.conf
reader, so they run without a mounted VFS while covering exactly the value
handling the boot path depends on.

## Scenarios

### rc.conf screen_type normalization

#### defaults to wm when the key (or the whole file) is absent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults to wm when the key (or the whole file) is absent
- Look up screen_type on a system that never staged rc.conf


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defaults to wm when the key (or the whole file) is absent")
step("Look up screen_type on a system that never staged rc.conf")
assert_equal(rc_conf_normalize_screen_type(nil), "wm")
```

</details>

#### accepts each of the four supported screen types

- accepts each of the four supported screen types
- Normalize every documented screen type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts each of the four supported screen types")
step("Normalize every documented screen type")
assert_equal(rc_conf_normalize_screen_type("wm"), "wm")
assert_equal(rc_conf_normalize_screen_type("2d"), "2d")
assert_equal(rc_conf_normalize_screen_type("web"), "web")
assert_equal(rc_conf_normalize_screen_type("gui"), "gui")
```

</details>

#### trims surrounding space and lowercases the value

- trims surrounding space and lowercases the value
- Normalize a sloppily written value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("trims surrounding space and lowercases the value")
step("Normalize a sloppily written value")
assert_equal(rc_conf_normalize_screen_type("  GUI "), "gui")
```

</details>

#### falls back to wm on an unrecognized value

- falls back to wm on an unrecognized value
- Ask for a screen type that does not exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back to wm on an unrecognized value")
step("Ask for a screen type that does not exist")
assert_equal(rc_conf_normalize_screen_type("quake"), "wm")
```

</details>

#### falls back to wm on an empty value

- falls back to wm on an empty value
- Write screen_type= with nothing after it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back to wm on an empty value")
step("Write screen_type= with nothing after it")
assert_equal(rc_conf_normalize_screen_type(""), "wm")
```

</details>

### rc.conf screen_res parsing

#### uses the caller's defaults when the key is absent

- uses the caller's defaults when the key is absent
- Parse a missing screen_res against the historical BGA mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses the caller's defaults when the key is absent")
step("Parse a missing screen_res against the historical BGA mode")
val res = rc_conf_parse_screen_res(nil, 1024, 768)
assert_equal(res.0, 1024)
assert_equal(res.1, 768)
```

</details>

#### parses a WxH value

- parses a WxH value
- Request a 1080p boot console


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("parses a WxH value")
step("Request a 1080p boot console")
val res = rc_conf_parse_screen_res("1920x1080", 1024, 768)
assert_equal(res.0, 1920)
assert_equal(res.1, 1080)
```

</details>

#### falls back to the defaults on malformed input

- falls back to the defaults on malformed input
- Write junk into screen_res


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back to the defaults on malformed input")
step("Write junk into screen_res")
val res = rc_conf_parse_screen_res("junk", 1024, 768)
assert_equal(res.0, 1024)
assert_equal(res.1, 768)
```

</details>

#### rejects an out-of-range resolution

- rejects an out-of-range resolution
- Ask for a resolution beyond the 8192 guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an out-of-range resolution")
step("Ask for a resolution beyond the 8192 guard")
val res = rc_conf_parse_screen_res("99999x99999", 1024, 768)
assert_equal(res.0, 1024)
assert_equal(res.1, 768)
```

</details>

### rc.conf screen_simd normalization

#### defaults to auto when unset

- defaults to auto when unset


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defaults to auto when unset")
assert_equal(rc_conf_normalize_screen_simd(nil), "auto")
```

</details>

#### accepts on and off

- accepts on and off


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts on and off")
assert_equal(rc_conf_normalize_screen_simd("on"), "on")
assert_equal(rc_conf_normalize_screen_simd("OFF"), "off")
```

</details>

#### accepts the explicit ISA kernel families WS-D pins

- accepts the explicit ISA kernel families WS-D pins


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts the explicit ISA kernel families WS-D pins")
assert_equal(rc_conf_normalize_screen_simd("sse2"), "sse2")
assert_equal(rc_conf_normalize_screen_simd("AVX2"), "avx2")
assert_equal(rc_conf_normalize_screen_simd(" neon "), "neon")
```

</details>

#### falls back to auto on an unrecognized value

- falls back to auto on an unrecognized value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back to auto on an unrecognized value")
assert_equal(rc_conf_normalize_screen_simd("turbo"), "auto")
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


## Related Documentation

- **Plan:** `doc/03_plan/os/simpleos/screens/ws_a_config_screen_selection_detail.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2f822e66a4dad6deb2194e53e644f2d647624f0ceddca38c0d0de01569fbd9fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f822e66a4dad6deb2194e53e644f2d647624f0ceddca38c0d0de01569fbd9fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f822e66a4dad6deb2194e53e644f2d647624f0ceddca38c0d0de01569fbd9fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/boot/rc_conf_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/boot/rc_conf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/boot/rc_conf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/boot/rc_conf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/boot/rc_conf_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to wm when the key (or the whole file) is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/rc_conf_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts each of the four supported screen types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/rc_conf_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims surrounding space and lowercases the value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
