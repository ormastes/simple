# Wine Kernel32 Module Loader Specification

> Tests covering Wine KERNEL32 module loader bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Module Loader Specification

## Scenarios

### Wine KERNEL32 module loader bridge

#### models DLL search order without host filesystem access or DLL execution

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models DLL search order without host filesystem access or DLL execution
   - Expected: result.ok is true
   - Expected: result.search_roots.len() equals `8`
   - Expected: result.search_roots[0] equals `\\KnownDlls`
   - Expected: result.search_roots[1] equals `C:\\Games`
   - Expected: result.search_roots[6] equals `D:\\GameBin`
   - Expected: result.candidate_paths[0] equals `\\KnownDlls\\kernel32.dll`
   - Expected: result.candidate_paths[1] equals `C:\\Games\\kernel32.dll`
   - Expected: result.selected_path equals `\\KnownDlls\\kernel32.dll`
   - Expected: result.status equals `dll-search-order-modeled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("models DLL search order without host filesystem access or DLL execution")
val result = wine_kernel32_plan_dll_search_order(
    "kernel32.dll",
    "C:\\Games",
    "C:\\Users\\Player",
    ["D:\\GameBin", "E:\\Shared"],
    ["kernel32.dll", "ntdll.dll"]
)

expect(result.ok).to_equal(true)
expect(result.search_roots.len()).to_equal(8)
expect(result.search_roots[0]).to_equal("\\KnownDlls")
expect(result.search_roots[1]).to_equal("C:\\Games")
expect(result.search_roots[6]).to_equal("D:\\GameBin")
expect(result.candidate_paths[0]).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.candidate_paths[1]).to_equal("C:\\Games\\kernel32.dll")
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.evidence).to_contain("dll-search-order-modeled")
expect(result.evidence).to_contain("no-host-filesystem-access")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.status).to_equal("dll-search-order-modeled")
```

</details>

#### uses application directory first for non-KnownDll basenames

- uses application directory first for non-KnownDll basenames
   - Expected: result.ok is true
   - Expected: result.selected_path equals `C:\\Games\\gameaudio.dll`
   - Expected: result.candidate_paths[0] equals `\\KnownDlls\\gameaudio.dll`
   - Expected: result.candidate_paths[1] equals `C:\\Games\\gameaudio.dll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses application directory first for non-KnownDll basenames")
val result = wine_kernel32_plan_dll_search_order("gameaudio.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"])

expect(result.ok).to_equal(true)
expect(result.selected_path).to_equal("C:\\Games\\gameaudio.dll")
expect(result.candidate_paths[0]).to_equal("\\KnownDlls\\gameaudio.dll")
expect(result.candidate_paths[1]).to_equal("C:\\Games\\gameaudio.dll")
```

</details>

#### rejects DLL search inputs that would escape the modeled basename lane

- rejects DLL search inputs that would escape the modeled basename lane
   - Expected: absolute.ok is false
   - Expected: absolute.error equals `dll-name-must-be-basename`
   - Expected: missing_suffix.ok is false
   - Expected: missing_suffix.error equals `dll-name-must-end-with-dll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects DLL search inputs that would escape the modeled basename lane")
val absolute = wine_kernel32_plan_dll_search_order("C:\\Windows\\System32\\kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"])
expect(absolute.ok).to_equal(false)
expect(absolute.error).to_equal("dll-name-must-be-basename")

val missing_suffix = wine_kernel32_plan_dll_search_order("kernel32", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"])
expect(missing_suffix.ok).to_equal(false)
expect(missing_suffix.error).to_equal("dll-name-must-end-with-dll")
```

</details>

#### executes a bounded module and procedure resolution sequence

- executes a bounded module and procedure resolution sequence
   - Expected: result.ok is true
   - Expected: result.handle equals `0x120`
   - Expected: result.proc_address equals `0x120000 + 3`
   - Expected: result.operations equals `GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary`
   - Expected: wine_kernel32_get_module_handle_w(result.table, "kernel32.dll").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded module and procedure resolution sequence")
val result = wine_kernel32_execute_module_resolution(
    ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "KERNEL32.dll",
    "GetProcAddress"
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary")
expect(wine_kernel32_get_module_handle_w(result.table, "kernel32.dll").ok).to_equal(true)
```

</details>

#### executes a bounded LoadLibraryExW module resolution sequence

- executes a bounded LoadLibraryExW module resolution sequence
   - Expected: result.ok is true
   - Expected: result.handle equals `0x120`
   - Expected: result.proc_address equals `0x120000 + 3`
   - Expected: result.operations equals `GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded LoadLibraryExW module resolution sequence")
val result = wine_kernel32_execute_module_resolution_ex(
    ["GetModuleHandleW", "LoadLibraryExW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "GetProcAddress",
    0
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
```

</details>

#### keeps module loader dispatch ordered and bounded

- keeps module loader dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-module-loader-sequence-expected:GetModuleHandleW`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:VirtualAlloc`
   - Expected: wrong_ex_order.ok is false
   - Expected: wrong_ex_order.error equals `kernel32-module-loader-sequence-expected:LoadLibraryExW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps module loader dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_module_resolution(
    ["LoadLibraryW", "GetModuleHandleW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "GetProcAddress"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-module-loader-sequence-expected:GetModuleHandleW")

val wrong_family = wine_kernel32_execute_module_resolution(
    ["GetModuleHandleW", "LoadLibraryW", "VirtualAlloc", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "GetProcAddress"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:VirtualAlloc")

val wrong_ex_order = wine_kernel32_execute_module_resolution_ex(
    ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "GetProcAddress",
    0
)
expect(wrong_ex_order.ok).to_equal(false)
expect(wrong_ex_order.error).to_equal("kernel32-module-loader-sequence-expected:LoadLibraryExW")
```

</details>

#### reports missing modules, missing procedures, and invalid handles

- reports missing modules, missing procedures, and invalid handles
   - Expected: missing_module.ok is false
   - Expected: missing_module.error equals `GetModuleHandleW:module-not-loaded`
   - Expected: missing_proc.ok is false
   - Expected: missing_proc.error equals `GetProcAddress:proc-not-found`
   - Expected: invalid_handle.ok is false
   - Expected: invalid_handle.error equals `invalid-module-handle`
   - Expected: unsupported_flags.ok is false
   - Expected: unsupported_flags.error equals `unsupported-load-flags`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports missing modules, missing procedures, and invalid handles")
val missing_module = wine_kernel32_execute_module_resolution(
    ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "user32.dll",
    "MessageBoxW"
)
expect(missing_module.ok).to_equal(false)
expect(missing_module.error).to_equal("GetModuleHandleW:module-not-loaded")

val missing_proc = wine_kernel32_execute_module_resolution(
    ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "UnknownProc"
)
expect(missing_proc.ok).to_equal(false)
expect(missing_proc.error).to_equal("GetProcAddress:proc-not-found")

val invalid_handle = wine_kernel32_get_proc_address(_table(), 0x999, "GetProcAddress")
expect(invalid_handle.ok).to_equal(false)
expect(invalid_handle.error).to_equal("invalid-module-handle")

val unsupported_flags = wine_kernel32_load_library_ex_w(_table(), "kernel32.dll", 8)
expect(unsupported_flags.ok).to_equal(false)
expect(unsupported_flags.error).to_equal("unsupported-load-flags")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_kernel32_module_loader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 module loader bridge.
- Wine KERNEL32 module loader bridge

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `beb439070f2e4b326eb60b568277436ad2249d5978366a2452a868e8dffdc4ae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `beb439070f2e4b326eb60b568277436ad2249d5978366a2452a868e8dffdc4ae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `beb439070f2e4b326eb60b568277436ad2249d5978366a2452a868e8dffdc4ae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/wine_kernel32_module_loader_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_kernel32_module_loader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_kernel32_module_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_kernel32_module_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_kernel32_module_loader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_kernel32_module_loader_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models DLL search order without host filesystem access or DLL execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_module_loader_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses application directory first for non-KnownDll basenames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_module_loader_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects DLL search inputs that would escape the modeled basename lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
