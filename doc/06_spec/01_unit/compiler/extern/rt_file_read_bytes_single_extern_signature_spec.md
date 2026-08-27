# rt_file_read_bytes_single_extern_signature_spec

> Purpose: Prove that rt_file_read_bytes has a single extern signature.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rt_file_read_bytes_single_extern_signature_spec

Purpose: Prove that rt_file_read_bytes has a single extern signature.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that rt_file_read_bytes has a single extern signature.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### rt_file_read_bytes has a single extern signature

#### positive control: the scanner finds the declarations that certainly exist

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- positive control: the scanner finds the declarations that certainly exist
- Verify: positive control: the scanner finds the declarations that certainly exist
   - Expected: decls_with_return("\\[u8\\]") >= 20 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("positive control: the scanner finds the declarations that certainly exist")
step("Verify: positive control: the scanner finds the declarations that certainly exist")
# @req: REQ-COMPILER-EXTERN-001
# There are dozens of `-> [u8]` declarations. Zero means the scan
# broke, not that the repo is clean.
expect(decls_with_return("\\[u8\\]") >= 20).to_equal(true)
```

</details>

#### negative control: the anchor does not match a return type nobody uses

- negative control: the anchor does not match a return type nobody uses
- Verify: negative control: the anchor does not match a return type nobody uses
   - Expected: decls_with_return("NoSuchReturnTypeXyzzy") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("negative control: the anchor does not match a return type nobody uses")
step("Verify: negative control: the anchor does not match a return type nobody uses")
expect(decls_with_return("NoSuchReturnTypeXyzzy")).to_equal(0)
```

</details>

#### control: the scan produces a non-empty type set

- control: the scan produces a non-empty type set
- Verify: control: the scan produces a non-empty type set
   - Expected: decl_return_types() == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("control: the scan produces a non-empty type set")
step("Verify: control: the scan produces a non-empty type set")
# Distinguishes "clean" from "the command errored and printed nothing".
expect(decl_return_types() == "").to_equal(false)
```

</details>

#### no module declares the raw i64 handle form

- no module declares the raw i64 handle form
- Verify: no module declares the raw i64 handle form
   - Expected: decls_with_return("i64") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("no module declares the raw i64 handle form")
step("Verify: no module declares the raw i64 handle form")
# `-> i64` skipped array decoding entirely and exposed the tagged
# pointer. Removed from src/compiler_rust/lib/std/src/sys/sffi/io.spl.
expect(decls_with_return("i64")).to_equal(0)
```

</details>

#### no module declares a List<i32> element width

- no module declares a List<i32> element width
- Verify: no module declares a List<i32> element width
   - Expected: decls_with_return("List<i32>") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("no module declares a List<i32> element width")
step("Verify: no module declares a List<i32> element width")
# `List<i32>` decodes 4-byte elements out of a 1-byte-element array.
# Converged in src/compiler_rust/lib/std/src/infra/file_io.spl.
expect(decls_with_return("List<i32>")).to_equal(0)
```

</details>

#### declares exactly one return type repo-wide

- declares exactly one return type repo-wide
- Verify: declares exactly one return type repo-wide
   - Expected: decl_return_types() equals `[u8]`
   - Expected: decl_type_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares exactly one return type repo-wide")
step("Verify: declares exactly one return type repo-wide")
# Surfacing the type set makes a failure self-diagnosing: it names the
# shapes that are still disagreeing.
expect(decl_return_types()).to_equal("[u8]")
expect(decl_type_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### the one return type matches the C runtime ABI

- the one return type matches the C runtime ABI
- Verify: the one return type matches the C runtime ABI
   - Expected: shell_output(cmd).trim().to_i64() >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the one return type matches the C runtime ABI")
step("Verify: the one return type matches the C runtime ABI")
# Not "whatever the declarations agree on" -- what the C actually
# returns. `rt_byte_array_new_len` is the byte-array constructor.
val cmd = "/usr/bin/grep -c 'rt_byte_array_new_len' src/runtime/runtime_native.c"
expect(shell_output(cmd).trim().to_i64() >= 1).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-EXTERN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cfd618b9520ada1c4718f1a1f2244bd84f32dc9ab9c98733de58ed7e32a87da8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cfd618b9520ada1c4718f1a1f2244bd84f32dc9ab9c98733de58ed7e32a87da8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cfd618b9520ada1c4718f1a1f2244bd84f32dc9ab9c98733de58ed7e32a87da8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl
mirror: doc/06_spec/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive control: the scanner finds the declarations that certainly exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negative control: the anchor does not match a return type nobody uses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: the scan produces a non-empty type set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
