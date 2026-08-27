# Stage4 Runtime Legacy Compat Provider Specification

> Tests covering Stage4 localized runtime legacy compatibility provider.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage4 Runtime Legacy Compat Provider Specification

## Scenarios

### Stage4 localized runtime legacy compatibility provider

#### names the exact compatibility archive for every hosted object ABI

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- names the exact compatibility archive for every hosted object ABI
   - Expected: stage4_runtime_legacy_compat_archive_file("linux", false).unwrap() equals `libsimple_stage4_runtime_legacy_compat.a`
   - Expected: stage4_runtime_legacy_compat_archive_file("macos", false).unwrap() equals `libsimple_stage4_runtime_legacy_compat.a`
   - Expected: stage4_runtime_legacy_compat_archive_file("freebsd", false).unwrap() equals `libsimple_stage4_runtime_legacy_compat.a`
   - Expected: stage4_runtime_legacy_compat_archive_file("windows", false).unwrap() equals `libsimple_stage4_runtime_legacy_compat.a`
   - Expected: stage4_runtime_legacy_compat_archive_file("windows", true).unwrap() equals `simple_stage4_runtime_legacy_compat.lib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the exact compatibility archive for every hosted object ABI")
expect(stage4_runtime_legacy_compat_archive_file("linux", false).unwrap()).to_equal("libsimple_stage4_runtime_legacy_compat.a")
expect(stage4_runtime_legacy_compat_archive_file("macos", false).unwrap()).to_equal("libsimple_stage4_runtime_legacy_compat.a")
expect(stage4_runtime_legacy_compat_archive_file("freebsd", false).unwrap()).to_equal("libsimple_stage4_runtime_legacy_compat.a")
expect(stage4_runtime_legacy_compat_archive_file("windows", false).unwrap()).to_equal("libsimple_stage4_runtime_legacy_compat.a")
expect(stage4_runtime_legacy_compat_archive_file("windows", true).unwrap()).to_equal("simple_stage4_runtime_legacy_compat.lib")
expect(stage4_runtime_legacy_compat_archive_file("linux", true).is_err()).to_be(true)
expect(stage4_runtime_legacy_compat_archive_file("plan9", false).is_err()).to_be(true)
```

</details>

#### maps each hosted ABI to its exact portable symbol format

- maps each hosted ABI to its exact portable symbol format
   - Expected: stage4_runtime_legacy_compat_object_format("linux", false).unwrap() equals `elf`
   - Expected: stage4_runtime_legacy_compat_object_format("freebsd", false).unwrap() equals `elf`
   - Expected: stage4_runtime_legacy_compat_object_format("macos", false).unwrap() equals `macho`
   - Expected: stage4_runtime_legacy_compat_object_format("windows", false).unwrap() equals `coff-mingw`
   - Expected: stage4_runtime_legacy_compat_object_format("windows", true).unwrap() equals `coff-msvc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps each hosted ABI to its exact portable symbol format")
expect(stage4_runtime_legacy_compat_object_format("linux", false).unwrap()).to_equal("elf")
expect(stage4_runtime_legacy_compat_object_format("freebsd", false).unwrap()).to_equal("elf")
expect(stage4_runtime_legacy_compat_object_format("macos", false).unwrap()).to_equal("macho")
expect(stage4_runtime_legacy_compat_object_format("windows", false).unwrap()).to_equal("coff-mingw")
expect(stage4_runtime_legacy_compat_object_format("windows", true).unwrap()).to_equal("coff-msvc")
expect(stage4_runtime_legacy_compat_object_format("linux", true).is_err()).to_be(true)
expect(stage4_runtime_legacy_compat_object_format("plan9", false).is_err()).to_be(true)
```

</details>

#### exposes only the audited safe 21-symbol compatibility ABI

- exposes only the audited safe 21-symbol compatibility ABI
   - Expected: exports.len() equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("exposes only the audited safe 21-symbol compatibility ABI")
val exports = stage4_runtime_legacy_compat_exports()
expect(exports.len()).to_equal(21)
for symbol in [
    "spl_strdup", "spl_str_new", "spl_str_len", "spl_str_cmp",
    "spl_str_concat", "spl_str_slice", "spl_str_index_of", "spl_str_replace",
    "spl_print", "spl_println", "spl_panic", "spl_file_read", "rt_is_dir",
    "rt_dir_remove_all", "rt_getcwd", "rt_mprotect", "rt_munmap_raw",
    "spl_env_get", "rt_sleep_ms_native",
    "rt_process_spawn_async", "rt_process_spawn_guarded"
]:
    expect(exports).to_contain(symbol)
for symbol in legacy_localized_symbols():
    expect(exports.contains(symbol)).to_be(false)
```

</details>

#### accepts the exact safe ABI after localization on ELF Mach-O and both COFF ABIs

- accepts the exact safe ABI after localization on ELF Mach-O and both COFF ABIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts the exact safe ABI after localization on ELF Mach-O and both COFF ABIs")
for object_format in ["elf", "macho", "coff-msvc", "coff-mingw"]:
    val localized = legacy_nm(stage4_runtime_legacy_compat_exports(), object_format, true)
    expect(stage4_validate_runtime_legacy_compat_symbol_contract(localized, object_format).is_ok()).to_be(true)
expect(stage4_validate_runtime_legacy_compat_symbol_contract(legacy_nm(stage4_runtime_legacy_compat_exports(), "elf", true), "wasm").is_err()).to_be(true)
```

</details>

#### accepts the supported undecorated MinGW x64 symbol shape

- accepts the supported undecorated MinGW x64 symbol shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts the supported undecorated MinGW x64 symbol shape")
val localized = legacy_nm(stage4_runtime_legacy_compat_exports(), "coff-msvc", true)
expect(stage4_validate_runtime_legacy_compat_symbol_contract(localized, "coff-mingw").is_ok()).to_be(true)
val raw = legacy_raw_nm("coff-msvc")
val localize = stage4_runtime_legacy_compat_localization_symbols(raw, "coff-mingw").unwrap()
expect(localize).to_contain("spl_array_new")
expect(localize.contains("_spl_array_new")).to_be(false)
```

</details>

#### localizes every known non-export definition on each hosted ABI

- localizes every known non-export definition on each hosted ABI
   - Expected: localized.len() equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("localizes every known non-export definition on each hosted ABI")
for object_format in ["elf", "macho", "coff-msvc", "coff-mingw"]:
    val localized = stage4_runtime_legacy_compat_localization_symbols(legacy_raw_nm(object_format), object_format).unwrap()
    expect(localized.len()).to_equal(28)
    for symbol in legacy_localized_symbols():
        expect(localized).to_contain(legacy_raw_symbol(symbol, object_format))
    for symbol in stage4_runtime_legacy_compat_exports():
        expect(localized.contains(legacy_raw_symbol(symbol, object_format))).to_be(false)
```

</details>

#### rejects missing or duplicate exports and localizes unknown definitions

- rejects missing or duplicate exports and localizes unknown definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects missing or duplicate exports and localizes unknown definitions")
for object_format in ["elf", "macho", "coff-msvc", "coff-mingw"]:
    val raw = legacy_raw_nm(object_format)
    val missing_row = "00000000 T " + legacy_raw_symbol("spl_str_new", object_format) + "\n"
    val duplicate_row = "00000000 T " + legacy_raw_symbol("spl_str_new", object_format) + "\n"
    val unknown_runtime_row = "00000000 T " + legacy_raw_symbol("spl_hidden", object_format) + "\n"
    val unknown_foreign_row = "00000000 T " + legacy_raw_symbol("foreign_helper", object_format) + "\n"
    expect(stage4_runtime_legacy_compat_localization_symbols(raw.replace(missing_row, ""), object_format).is_err()).to_be(true)
    expect(stage4_runtime_legacy_compat_localization_symbols(raw + duplicate_row, object_format).is_err()).to_be(true)
    val runtime_localize = stage4_runtime_legacy_compat_localization_symbols(raw + unknown_runtime_row, object_format).unwrap()
    val foreign_localize = stage4_runtime_legacy_compat_localization_symbols(raw + unknown_foreign_row, object_format).unwrap()
    expect(runtime_localize).to_contain(legacy_raw_symbol("spl_hidden", object_format))
    expect(foreign_localize).to_contain(legacy_raw_symbol("foreign_helper", object_format))
```

</details>

#### rejects array dict split and thread globals after localization

- rejects array dict split and thread globals after localization


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects array dict split and thread globals after localization")
for object_format in ["elf", "macho", "coff-msvc", "coff-mingw"]:
    val exact = legacy_nm(stage4_runtime_legacy_compat_exports(), object_format, true)
    for forbidden in ["spl_array_new", "spl_dict_set", "spl_str_split", "spl_thread_cpu_count"]:
        val row = "00000000 T " + legacy_raw_symbol(forbidden, object_format) + "\n"
        expect(stage4_validate_runtime_legacy_compat_symbol_contract(exact + row, object_format).is_err()).to_be(true)
```

</details>

#### requires rt_value_bool as the sole runtime dependency before and after localization

- requires rt_value_bool as the sole runtime dependency before and after localization


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("requires rt_value_bool as the sole runtime dependency before and after localization")
for object_format in ["elf", "macho", "coff-msvc", "coff-mingw"]:
    val raw = legacy_raw_nm(object_format)
    val exact = legacy_nm(stage4_runtime_legacy_compat_exports(), object_format, true)
    val value_bool_row = "         U " + legacy_raw_symbol("rt_value_bool", object_format) + "\n"
    val hidden_row = "         U " + legacy_raw_symbol("spl_hidden", object_format) + "\n"
    expect(stage4_runtime_legacy_compat_localization_symbols(raw, object_format).is_ok()).to_be(true)
    expect(stage4_validate_runtime_legacy_compat_symbol_contract(exact, object_format).is_ok()).to_be(true)
    expect(stage4_runtime_legacy_compat_localization_symbols(raw.replace(value_bool_row, ""), object_format).is_err()).to_be(true)
    expect(stage4_runtime_legacy_compat_localization_symbols(raw + hidden_row, object_format).is_err()).to_be(true)
    expect(stage4_validate_runtime_legacy_compat_symbol_contract(exact.replace(value_bool_row, ""), object_format).is_err()).to_be(true)
    expect(stage4_validate_runtime_legacy_compat_symbol_contract(exact + hidden_row, object_format).is_err()).to_be(true)
```

</details>

#### resolves both emitted compatibility roots and the transitive runtime cycle

- resolves both emitted compatibility roots and the transitive runtime cycle
   - Expected: selected equals `[0, 1]`
   - Expected: direct_selected equals `[0, 1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves both emitted compatibility roots and the transitive runtime cycle")
val labels = ["runtime_native", "runtime_legacy_compat"]
val scans = [
    "00000000 T rt_http_get\n00000010 T rt_value_bool\n         U spl_str_len",
    "00000000 T spl_str_len\n         U rt_value_bool"
]
val (selected, owners) = stage4_resolve_requested_archive_owners(["rt_http_get"], labels, scans, false).unwrap()
expect(selected).to_equal([0, 1])
expect(owners).to_contain("rt_http_get=runtime_native")
expect(owners).to_contain("spl_str_len=runtime_legacy_compat")
expect(owners).to_contain("rt_value_bool=runtime_native")
val (direct_selected, direct_owners) = stage4_resolve_requested_archive_owners(["spl_str_len"], labels, scans, false).unwrap()
expect(direct_selected).to_equal([0, 1])
expect(direct_owners).to_contain("spl_str_len=runtime_legacy_compat")
```

</details>

#### builds localizes admits and cleans only the dedicated compatibility archive

- builds localizes admits and cleans only the dedicated compatibility archive


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds localizes admits and cleans only the dedicated compatibility archive")
val source = compiler_native_link_source()
val strict_start = source.find("if stage4_requested:")
val strict_end = source.find("# Step 3: Combine all objects and link")
val strict_source = if strict_start >= 0 and strict_end > strict_start: source.substring(strict_start, strict_end) else: ""
val build_pos = strict_source.find("llvm_stage4_build_runtime_legacy_compat_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
val labels_pos = strict_source.find("\"runtime_native\", \"runtime_legacy_compat\"")
val paths_pos = strict_source.find("runtime_native_archive, runtime_legacy_compat_archive")
val owner_pos = strict_source.find("stage4_resolve_requested_archive_owners(stage4_requested_symbols, candidate_labels, candidate_scans, hosted_os == \"macos\")")
expect(source).to_contain("fn llvm_stage4_build_runtime_legacy_compat_archive")
expect(source).to_contain("stage4_runtime_legacy_compat_localization_symbols")
expect(source).to_contain("stage4_validate_runtime_legacy_compat_symbol_contract")
expect(build_pos).to_be_greater_than(-1)
expect(labels_pos).to_be_greater_than(build_pos)
expect(paths_pos).to_be_greater_than(build_pos)
expect(owner_pos).to_be_greater_than(paths_pos)
expect(strict_source.split("file_delete(runtime_legacy_compat_archive)").len() - 1).to_be_greater_than(4)
expect(strict_source.contains("candidate_paths = candidate_paths.push(runtime_legacy_core")).to_be(false)
expect(source.contains("llvm_stage4_build_single_object_provider_archive(runtime_objects, \"runtime_legacy_core\"")).to_be(false)
```

</details>

#### compiles a fresh legacy object but never admits its raw archive

- compiles a fresh legacy object but never admits its raw archive


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compiles a fresh legacy object but never admits its raw archive")
val compile_source = rt_file_read_text("src/compiler/70.backend/backend/runtime_compiler.spl") ?? ""
val link_source = compiler_native_link_source()
expect(compile_source).to_contain("if include_stage4_legacy_compat:\n        sources = sources.push(\"runtime_legacy_core\")\n        objects = objects.push(\"{{object_prefix}}runtime_legacy_core{{ext}}\")")
expect(link_source).to_contain("stage4_runtime_provider_object_matches(object, \"runtime_legacy_core\"")
expect(link_source.contains("candidate_labels = candidate_labels.push(\"runtime_legacy_core\")")).to_be(false)
expect(link_source.contains("candidate_paths = candidate_paths.push(runtime_legacy_core_archive)")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage4 localized runtime legacy compatibility provider.
- Stage4 localized runtime legacy compatibility provider

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5074e96ab9432ccba0fbdf248afabd523374b81e01b0b29109312bf1f1d3aadb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5074e96ab9432ccba0fbdf248afabd523374b81e01b0b29109312bf1f1d3aadb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5074e96ab9432ccba0fbdf248afabd523374b81e01b0b29109312bf1f1d3aadb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=30
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the exact compatibility archive for every hosted object ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps each hosted ABI to its exact portable symbol format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes only the audited safe 21-symbol compatibility ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
