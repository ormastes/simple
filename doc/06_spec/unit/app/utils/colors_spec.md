# colors_spec

> As a CLI developer I rely on the ANSI color utilities to emit exact escape

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# colors_spec

As a CLI developer I rely on the ANSI color utilities to emit exact escape

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/utils/colors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a CLI developer I rely on the ANSI color utilities to emit exact escape
sequences, so that terminal output is colored predictably and strippable.

## Scenarios

### colors

#### emits the ASCII escape character

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- call esc_char and assert code point 27


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call esc_char and assert code point 27")
assert_equal(colors.esc_char(), "\x1b")
```

</details>

#### emits reset and attribute codes

- reset/bold/dim/underline render as CSI sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset/bold/dim/underline render as CSI sequences")
assert_equal(colors.reset(), "\x1b[0m")
assert_equal(colors.bold(), "\x1b[1m")
assert_equal(colors.dim(), "\x1b[2m")
assert_equal(colors.underline(), "\x1b[4m")
```

</details>

#### generates foreground colors

- black..white map to CSI 30..37


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("black..white map to CSI 30..37")
assert_equal(colors.black(), "\x1b[30m")
assert_equal(colors.red(), "\x1b[31m")
assert_equal(colors.green(), "\x1b[32m")
assert_equal(colors.yellow(), "\x1b[33m")
assert_equal(colors.blue(), "\x1b[34m")
assert_equal(colors.magenta(), "\x1b[35m")
assert_equal(colors.cyan(), "\x1b[36m")
assert_equal(colors.white(), "\x1b[37m")
```

</details>

#### generates background colors

- bg_black..bg_white map to CSI 40..47


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bg_black..bg_white map to CSI 40..47")
assert_equal(colors.bg_black(), "\x1b[40m")
assert_equal(colors.bg_red(), "\x1b[41m")
assert_equal(colors.bg_green(), "\x1b[42m")
assert_equal(colors.bg_yellow(), "\x1b[43m")
assert_equal(colors.bg_blue(), "\x1b[44m")
assert_equal(colors.bg_magenta(), "\x1b[45m")
assert_equal(colors.bg_cyan(), "\x1b[46m")
assert_equal(colors.bg_white(), "\x1b[47m")
```

</details>

#### wraps text with semantic colors

- semantic wrappers bracket the payload with color + reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semantic wrappers bracket the payload with color + reset")
assert_equal(colors.success("ok"), "\x1b[32mok\x1b[0m")
assert_equal(colors.error("bad"), "\x1b[31mbad\x1b[0m")
assert_equal(colors.warning("warn"), "\x1b[33mwarn\x1b[0m")
assert_equal(colors.info("note"), "\x1b[36mnote\x1b[0m")
assert_equal(colors.debug("dbg"), "\x1b[2mdbg\x1b[0m")
assert_equal(colors.colorize("x", colors.blue), "\x1b[34mx\x1b[0m")
```

</details>

#### strips color codes from text

- strip_colors removes every wrapped sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strip_colors removes every wrapped sequence")
assert_equal(colors.strip_colors(colors.success("kept")), "kept")
assert_equal(colors.strip_colors("{colors.bold()}a{colors.reset()}{colors.bg_red()}b"), "ab")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d32cb5149b20f4feb283fcb1cc0cfed42481dfae0d7bf3c9918b79f64eede830`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d32cb5149b20f4feb283fcb1cc0cfed42481dfae0d7bf3c9918b79f64eede830`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d32cb5149b20f4feb283fcb1cc0cfed42481dfae0d7bf3c9918b79f64eede830`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/utils/colors_spec.spl
mirror: doc/06_spec/unit/app/utils/colors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/utils/colors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/utils/colors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/utils/colors_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the ASCII escape character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/utils/colors_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits reset and attribute codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/utils/colors_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates foreground colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
