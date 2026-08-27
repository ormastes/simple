# Stage 3 SEGFAULT Fix (LIM-010) Specification

> Verifies the fix for bootstrap Stage 3 SEGFAULT (exit 139) caused by duplicate LLVM CLI option registration. The fix changes strip_llvm_constructors() to return Result, replaces silent unwrap_or fallbacks with explicit warn!(), adds verify_stripped_archive() post-condition, and adds exit-139 detection in compile_stage().

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage 3 SEGFAULT Fix (LIM-010) Specification

Verifies the fix for bootstrap Stage 3 SEGFAULT (exit 139) caused by duplicate LLVM CLI option registration. The fix changes strip_llvm_constructors() to return Result, replaces silent unwrap_or fallbacks with explicit warn!(), adds verify_stripped_archive() post-condition, and adds exit-139 detection in compile_stage().

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | LIM-010 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/compiler/stage3_segfault_fix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the fix for bootstrap Stage 3 SEGFAULT (exit 139) caused by duplicate
LLVM CLI option registration. The fix changes strip_llvm_constructors() to return
Result, replaces silent unwrap_or fallbacks with explicit warn!(), adds
verify_stripped_archive() post-condition, and adds exit-139 detection in
compile_stage().

## Key Concepts

| Concept | Description |
|---------|-------------|
| LIM-010 | LLVM constructor conflict causing SEGFAULT at Stage 3 |
| strip_llvm_constructors | Function that removes .init_array/.ctors from archives |
| StripError | New error enum for stripping failure modes |
| verify_stripped_archive | Post-condition check that constructor sections are gone |
| VerifyOutcome | Distinguishes "verified clean" from "could not be checked" |

## Behavior

- strip_llvm_constructors() returns Result<PathBuf, StripError> instead of PathBuf
- The strip caller (linker.rs) propagates StripError with `map_err(..)?` and
  renders it via Display, which carries the LIM-010 tag and the remediation
- verify_stripped_archive() confirms no constructor sections remain after
  stripping, and reports Unverifiable — with a LIM-010 warning — rather than
  reporting success when no section-dump tool is available
- compile_stage() detects exit code 139 and emits LIM-010 diagnostic

## Correction (2026-08-05)

The original D-6 said "all 4 callsites in config.rs must replace
unwrap_or(native_all.clone()) with explicit match + warn!()". That describes a
layout which no longer exists: `strip_llvm_constructors` has exactly one caller
and it is in linker.rs, not config.rs, and no `unwrap_or(native_all.clone())`
exists anywhere in the tree. config.rs has no LIM-010 role at all, so the two
assertions that grepped config.rs for `warn!` and `LIM-010` were unsatisfiable
except by planting those literals. They now target the file that actually
implements silent-fallback elimination.

## Scenarios

### Stage3 SEGFAULT Fix — Source Structure

#### AC-2: tools.rs exists for strip_llvm_constructors changes

- AC-2: tools.rs exists for strip_llvm_constructors changes
   - Expected: file_exists("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: tools.rs exists for strip_llvm_constructors changes")
expect(file_exists("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")).to_equal(true)
```

</details>

#### AC-2: config.rs exists as the runtime-archive selector

- AC-2: config.rs exists as the runtime-archive selector
   - Expected: file_exists("src/compiler_rust/compiler/src/pipeline/native_project/config.rs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: config.rs exists as the runtime-archive selector")
expect(file_exists("src/compiler_rust/compiler/src/pipeline/native_project/config.rs")).to_equal(true)
```

</details>

#### AC-3: misc_commands.rs exists for compile_stage diagnostics

- AC-3: misc_commands.rs exists for compile_stage diagnostics
   - Expected: file_exists("src/compiler_rust/driver/src/cli/commands/misc_commands.rs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: misc_commands.rs exists for compile_stage diagnostics")
expect(file_exists("src/compiler_rust/driver/src/cli/commands/misc_commands.rs")).to_equal(true)
```

</details>

#### AC-2: native_all lib.rs exists as the archive source

- AC-2: native_all lib.rs exists as the archive source
   - Expected: file_exists("src/compiler_rust/native_all/src/lib.rs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: native_all lib.rs exists as the archive source")
expect(file_exists("src/compiler_rust/native_all/src/lib.rs")).to_equal(true)
```

</details>

### Stage3 SEGFAULT Fix — StripError and Result Return

#### AC-2: tools.rs contains StripError enum definition

- AC-2: tools.rs contains StripError enum definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: tools.rs contains StripError enum definition")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("StripError")
```

</details>

#### AC-2: StripError has ObjcopyNotFound variant

- AC-2: StripError has ObjcopyNotFound variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: StripError has ObjcopyNotFound variant")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("ObjcopyNotFound")
```

</details>

#### AC-2: StripError has ObjcopyFailed variant

- AC-2: StripError has ObjcopyFailed variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: StripError has ObjcopyFailed variant")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("ObjcopyFailed")
```

</details>

#### AC-2: StripError has VerificationFailed variant

- AC-2: StripError has VerificationFailed variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: StripError has VerificationFailed variant")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("VerificationFailed")
```

</details>

#### AC-2: strip_llvm_constructors returns Result

- AC-2: strip_llvm_constructors returns Result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: strip_llvm_constructors returns Result")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("Result<PathBuf, StripError>")
```

</details>

### Stage3 SEGFAULT Fix — Silent Fallback Elimination

#### AC-2: strip verification cannot report 'not checked' as success

- AC-2: strip verification cannot report 'not checked' as success


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: strip verification cannot report 'not checked' as success")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
# The Unverifiable variant is what makes the two outcomes distinguishable.
expect(content).to_contain("VerifyOutcome::Unverifiable")
expect(content).to_contain("warn!")
```

</details>

#### AC-2: the unverified-strip fallback diagnostic carries LIM-010

- AC-2: the unverified-strip fallback diagnostic carries LIM-010


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: the unverified-strip fallback diagnostic carries LIM-010")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("LIM-010")
```

</details>

### Stage3 SEGFAULT Fix — Archive Verification

#### AC-2: verify_stripped_archive function exists in tools.rs

- AC-2: verify_stripped_archive function exists in tools.rs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: verify_stripped_archive function exists in tools.rs")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("verify_stripped_archive")
```

</details>

#### AC-2: find_objdump_tool function exists in tools.rs

- AC-2: find_objdump_tool function exists in tools.rs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: find_objdump_tool function exists in tools.rs")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("find_objdump_tool")
```

</details>

#### AC-2: verification checks for .init_array section

- AC-2: verification checks for .init_array section


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: verification checks for .init_array section")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain(".init_array")
```

</details>

#### AC-2: verification checks for .ctors section

- AC-2: verification checks for .ctors section


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: verification checks for .ctors section")
val content = read_file_text("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain(".ctors")
```

</details>

### Stage3 SEGFAULT Fix — SIGSEGV Detection

#### AC-6: compile_stage detects exit code 139

- AC-6: compile_stage detects exit code 139


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-6: compile_stage detects exit code 139")
val content = read_file_text("src/compiler_rust/driver/src/cli/commands/misc_commands.rs")
expect(content).to_contain("139")
```

</details>

#### AC-6: SIGSEGV diagnostic references LIM-010

- AC-6: SIGSEGV diagnostic references LIM-010


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-6: SIGSEGV diagnostic references LIM-010")
val content = read_file_text("src/compiler_rust/driver/src/cli/commands/misc_commands.rs")
expect(content).to_contain("LIM-010")
```

</details>

#### AC-6: diagnostic mentions SEGFAULT

- AC-6: diagnostic mentions SEGFAULT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-6: diagnostic mentions SEGFAULT")
val content = read_file_text("src/compiler_rust/driver/src/cli/commands/misc_commands.rs")
expect(content).to_contain("SEGFAULT")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `17e0f08eca2b75daf0a9a6a9a2484d8c21ff5ff5cdcbdd142a26e3b8e99116bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17e0f08eca2b75daf0a9a6a9a2484d8c21ff5ff5cdcbdd142a26e3b8e99116bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17e0f08eca2b75daf0a9a6a9a2484d8c21ff5ff5cdcbdd142a26e3b8e99116bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/stage3_segfault_fix_spec.spl
mirror: doc/06_spec/03_system/compiler/stage3_segfault_fix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/stage3_segfault_fix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/stage3_segfault_fix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/stage3_segfault_fix_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: tools.rs exists for strip_llvm_constructors changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/stage3_segfault_fix_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: config.rs exists as the runtime-archive selector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/stage3_segfault_fix_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: misc_commands.rs exists for compile_stage diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
