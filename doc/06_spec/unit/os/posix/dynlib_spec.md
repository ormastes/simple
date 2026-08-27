# DynLibKind OOP Interface Specification

> Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DynLibKind OOP Interface Specification

Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/posix/dynlib_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE
dynamic library formats, including validity checks, format naming, path
extraction, and error handling for Invalid variants.

## Scenarios

### DynLibKind.Elf

#### reports valid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports valid
   - Expected: dynlib_is_valid(lib) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports valid")
val lib = DynLibKind.Elf(state: ElfLibState(
    handle: 1,
    base: 0,
    path: "/lib/libtest.so"
))
expect(dynlib_is_valid(lib)).to_equal(true)
```

</details>

#### returns correct format name

- returns correct format name
   - Expected: dynlib_format_name(lib) equals `ELF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct format name")
val lib = DynLibKind.Elf(state: ElfLibState(
    handle: 1,
    base: 0,
    path: "/lib/libtest.so"
))
expect(dynlib_format_name(lib)).to_equal("ELF")
```

</details>

#### returns correct path

- returns correct path
   - Expected: dynlib_path(lib) equals `/lib/libtest.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct path")
val lib = DynLibKind.Elf(state: ElfLibState(
    handle: 1,
    base: 0,
    path: "/lib/libtest.so"
))
expect(dynlib_path(lib)).to_equal("/lib/libtest.so")
```

</details>

### DynLibKind.Smf

#### reports valid

- reports valid
   - Expected: dynlib_is_valid(lib) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports valid")
val lib = DynLibKind.Smf(state: SmfLibState(
    handle: 2,
    path: "/lib/plugin.smf",
    stub_entry: 0
))
expect(dynlib_is_valid(lib)).to_equal(true)
```

</details>

#### returns correct format name

- returns correct format name
   - Expected: dynlib_format_name(lib) equals `SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct format name")
val lib = DynLibKind.Smf(state: SmfLibState(
    handle: 2,
    path: "/lib/plugin.smf",
    stub_entry: 0
))
expect(dynlib_format_name(lib)).to_equal("SMF")
```

</details>

#### returns correct path

- returns correct path
   - Expected: dynlib_path(lib) equals `/lib/plugin.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct path")
val lib = DynLibKind.Smf(state: SmfLibState(
    handle: 2,
    path: "/lib/plugin.smf",
    stub_entry: 0
))
expect(dynlib_path(lib)).to_equal("/lib/plugin.smf")
```

</details>

### DynLibKind.Pe

#### reports valid

- reports valid
   - Expected: dynlib_is_valid(lib) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports valid")
val lib = DynLibKind.Pe(state: PeLibState(
    handle: 3,
    path: "kernel32.dll",
    base: 0,
    image_size: 0
))
expect(dynlib_is_valid(lib)).to_equal(true)
```

</details>

#### returns correct format name

- returns correct format name
   - Expected: dynlib_format_name(lib) equals `PE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct format name")
val lib = DynLibKind.Pe(state: PeLibState(
    handle: 3,
    path: "kernel32.dll",
    base: 0,
    image_size: 0
))
expect(dynlib_format_name(lib)).to_equal("PE")
```

</details>

#### returns correct path

- returns correct path
   - Expected: dynlib_path(lib) equals `kernel32.dll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct path")
val lib = DynLibKind.Pe(state: PeLibState(
    handle: 3,
    path: "kernel32.dll",
    base: 0,
    image_size: 0
))
expect(dynlib_path(lib)).to_equal("kernel32.dll")
```

</details>

### DynLibKind.Invalid

#### reports not valid

- reports not valid
   - Expected: dynlib_is_valid(lib) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports not valid")
val lib = DynLibKind.Invalid
expect(dynlib_is_valid(lib)).to_equal(false)
```

</details>

#### returns empty path

- returns empty path
   - Expected: dynlib_path(lib) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty path")
val lib = DynLibKind.Invalid
expect(dynlib_path(lib)).to_equal("")
```

</details>

#### returns Invalid format name

- returns Invalid format name
   - Expected: dynlib_format_name(lib) equals `Invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Invalid format name")
val lib = DynLibKind.Invalid
expect(dynlib_format_name(lib)).to_equal("Invalid")
```

</details>

#### dynlib_symbol returns negative for Invalid

- dynlib_symbol returns negative for Invalid
   - Expected: result < 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dynlib_symbol returns negative for Invalid")
val lib = DynLibKind.Invalid
val result = dynlib_symbol(lib, "anything")
expect(result < 0).to_equal(true)
```

</details>

#### dynlib_close returns negative for Invalid

- dynlib_close returns negative for Invalid
   - Expected: result < 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dynlib_close returns negative for Invalid")
val lib = DynLibKind.Invalid
val result = dynlib_close(lib)
expect(result < 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `d946c791f066dc733ddf70ce9e171377179c5ad81486c6c4834ad70f4c7b63a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d946c791f066dc733ddf70ce9e171377179c5ad81486c6c4834ad70f4c7b63a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d946c791f066dc733ddf70ce9e171377179c5ad81486c6c4834ad70f4c7b63a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/posix/dynlib_spec.spl
mirror: doc/06_spec/unit/os/posix/dynlib_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/posix/dynlib_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/posix/dynlib_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/posix/dynlib_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/dynlib_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct format name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/dynlib_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
