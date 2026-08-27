# DynLibKind OOP Interface Specification

> Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DynLibKind OOP Interface Specification

Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/posix/dynlib_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE
dynamic library formats, including validity checks, format naming, path
extraction, and error handling for Invalid variants.

## Scenarios

### DynLibKind host formats

#### recognizes versioned ELF names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes versioned ELF names
   - Expected: dynlib_format_for_path("libc.so.7") equals `elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes versioned ELF names")
expect(dynlib_format_for_path("libc.so.7")).to_equal("elf")
```

</details>

#### recognizes Mach-O dylibs

- recognizes Mach-O dylibs
   - Expected: dynlib_format_for_path("libSystem.dylib") equals `macho`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes Mach-O dylibs")
expect(dynlib_format_for_path("libSystem.dylib")).to_equal("macho")
```

</details>

#### recognizes PE DLLs

- recognizes PE DLLs
   - Expected: dynlib_format_for_path("kernel32.dll") equals `pe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes PE DLLs")
expect(dynlib_format_for_path("kernel32.dll")).to_equal("pe")
```

</details>

#### rejects the zero failure sentinel before constructing a valid variant

- rejects the zero failure sentinel before constructing a valid variant
   - Expected: dynlib_handle_is_valid(0) is false
   - Expected: dynlib_handle_is_valid(-1) is false
   - Expected: dynlib_handle_is_valid(1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the zero failure sentinel before constructing a valid variant")
expect(dynlib_handle_is_valid(0)).to_equal(false)
expect(dynlib_handle_is_valid(-1)).to_equal(false)
expect(dynlib_handle_is_valid(1)).to_equal(true)
```

</details>

### DynLibKind.Elf

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

#### dynlib_symbol_is_process_callable returns false for Invalid

- dynlib_symbol_is_process_callable returns false for Invalid
   - Expected: dynlib_symbol_is_process_callable(lib, "anything") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dynlib_symbol_is_process_callable returns false for Invalid")
val lib = DynLibKind.Invalid
expect(dynlib_symbol_is_process_callable(lib, "anything")).to_equal(false)
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
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `e5def6f255ac47e994f04ed126602d46bd08452e7fd334a816cfa7353816f68f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5def6f255ac47e994f04ed126602d46bd08452e7fd334a816cfa7353816f68f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5def6f255ac47e994f04ed126602d46bd08452e7fd334a816cfa7353816f68f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/posix/dynlib_spec.spl
mirror: doc/06_spec/01_unit/os/posix/dynlib_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/posix/dynlib_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/posix/dynlib_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/posix/dynlib_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes versioned ELF names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/posix/dynlib_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes Mach-O dylibs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/posix/dynlib_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes PE DLLs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
