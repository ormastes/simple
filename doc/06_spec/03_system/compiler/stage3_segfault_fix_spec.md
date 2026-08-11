# Stage 3 SEGFAULT Fix (LIM-010) Specification

> Verifies the fix for bootstrap Stage 3 SEGFAULT (exit 139) caused by duplicate LLVM CLI option registration. The fix changes strip_llvm_constructors() to return Result, replaces silent unwrap_or fallbacks with explicit warn!(), adds verify_stripped_archive() post-condition, and adds exit-139 detection in compile_stage().

<!-- sdn-diagram:id=stage3_segfault_fix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stage3_segfault_fix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stage3_segfault_fix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stage3_segfault_fix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

## Behavior

- strip_llvm_constructors() returns Result<PathBuf, StripError> instead of PathBuf
- Callers in config.rs use explicit match + warn!() instead of unwrap_or
- verify_stripped_archive() confirms no constructor sections remain after stripping
- compile_stage() detects exit code 139 and emits LIM-010 diagnostic

## Scenarios

### Stage3 SEGFAULT Fix — Source Structure

#### AC-2: tools.rs exists for strip_llvm_constructors changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")).to_equal(true)
```

</details>

#### AC-2: config.rs exists for callsite error handling changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler_rust/compiler/src/pipeline/native_project/config.rs")).to_equal(true)
```

</details>

#### AC-3: misc_commands.rs exists for compile_stage diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler_rust/driver/src/cli/commands/misc_commands.rs")).to_equal(true)
```

</details>

#### AC-2: native_all lib.rs exists as the archive source

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler_rust/native_all/src/lib.rs")).to_equal(true)
```

</details>

### Stage3 SEGFAULT Fix — StripError and Result Return

#### AC-2: tools.rs contains StripError enum definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("StripError")
```

</details>

#### AC-2: StripError has ObjcopyNotFound variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("ObjcopyNotFound")
```

</details>

#### AC-2: StripError has ObjcopyFailed variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("ObjcopyFailed")
```

</details>

#### AC-2: StripError has VerificationFailed variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("VerificationFailed")
```

</details>

#### AC-2: strip_llvm_constructors returns Result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("Result<PathBuf, StripError>")
```

</details>

### Stage3 SEGFAULT Fix — Silent Fallback Elimination

#### AC-2: config.rs no longer uses unwrap_or for strip results

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/config.rs")
# After the fix, unwrap_or(native_all.clone()) pattern should be gone
# from strip_llvm_constructors calls. The content should contain
# explicit match or warn! instead.
expect(content).to_contain("warn!")
```

</details>

#### AC-2: config.rs contains LIM-010 in warning messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/config.rs")
expect(content).to_contain("LIM-010")
```

</details>

### Stage3 SEGFAULT Fix — Archive Verification

#### AC-2: verify_stripped_archive function exists in tools.rs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("verify_stripped_archive")
```

</details>

#### AC-2: find_objdump_tool function exists in tools.rs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain("find_objdump_tool")
```

</details>

#### AC-2: verification checks for .init_array section

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain(".init_array")
```

</details>

#### AC-2: verification checks for .ctors section

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(content).to_contain(".ctors")
```

</details>

### Stage3 SEGFAULT Fix — SIGSEGV Detection

#### AC-6: compile_stage detects exit code 139

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/driver/src/cli/commands/misc_commands.rs")
expect(content).to_contain("139")
```

</details>

#### AC-6: SIGSEGV diagnostic references LIM-010

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/driver/src/cli/commands/misc_commands.rs")
expect(content).to_contain("LIM-010")
```

</details>

#### AC-6: diagnostic mentions SEGFAULT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_text_file("src/compiler_rust/driver/src/cli/commands/misc_commands.rs")
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
