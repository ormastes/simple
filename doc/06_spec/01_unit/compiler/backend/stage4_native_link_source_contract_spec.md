# Contract spec: test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl` and a green Results line.

## Scenarios

### Stage4 split native linker source contracts

#### discovers the canonical native-all archive name for each hosted OS

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- discovers the canonical native-all archive name for each hosted OS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("discovers the canonical native-all archive name for each hosted OS")
val source = compiler_native_link_source()
expect(source).to_contain("if hosted_os == \"windows\" and not _is_mingw(): \"simple_native_all.lib\" else: \"libsimple_native_all.a\"")
```

</details>

#### builds a private deterministic compiler backfill capsule from the derived manifest

- builds a private deterministic compiler backfill capsule from the derived manifest
   - Expected: build_source.split("\"--remove-section=").len() - 1 equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds a private deterministic compiler backfill capsule from the derived manifest")
val source = compiler_native_link_source()
val build_pos = source.find("fn llvm_stage4_build_compiler_backfill_capsule")
val provider_pos = source.find("fn llvm_stage4_build_single_object_provider_archive")
expect(build_pos).to_be_greater_than(-1)
expect(provider_pos).to_be_greater_than(build_pos)
val build_source = source.substring(build_pos, provider_pos)
val raw_scan_pos = build_source.find("process_run(nm, [\"-g\", \"-p\", raw_archive])")
val manifest_pos = build_source.find("stage4_derive_compiler_backfill_manifest(raw_nm_out, object_format)")
val closure_pos = build_source.find("process_run(hosted_cc, closure_args)")
val localize_pos = build_source.find("stage4_compiler_backfill_localization_symbols(closure_nm_out, object_format, manifest)")
val objcopy_pos = build_source.find("process_run(objcopy, objcopy_args)")
val localized_fingerprint_pos = build_source.find("stage4_compiler_backfill_symbol_table_fingerprint(localized_nm_out)")
val archive_pos = build_source.find("process_run(archiver, [\"rcsD\", capsule_path, localized_object])")
val member_pos = build_source.find("members != \"compiler_backfill_local.o\"")
val inventory_pos = build_source.find("llvm_stage4_candidate_archive_inventory([\"compiler_backfill\"], [capsule_path])")
val envelope_pos = build_source.last_index_of("stage4_validate_compiler_backfill_symbol_envelope(scans[0], object_format)")
val final_fingerprint_pos = build_source.find("stage4_compiler_backfill_symbol_table_fingerprint(scans[0])")
val equality_pos = build_source.find("if final_symbol_fingerprint != localized_symbol_fingerprint:")
expect(raw_scan_pos).to_be_greater_than(-1)
expect(manifest_pos).to_be_greater_than(raw_scan_pos)
expect(closure_pos).to_be_greater_than(manifest_pos)
expect(localize_pos).to_be_greater_than(closure_pos)
expect(objcopy_pos).to_be_greater_than(localize_pos)
expect(localized_fingerprint_pos).to_be_greater_than(objcopy_pos)
expect(archive_pos).to_be_greater_than(localized_fingerprint_pos)
expect(member_pos).to_be_greater_than(archive_pos)
expect(inventory_pos).to_be_greater_than(member_pos)
expect(envelope_pos).to_be_greater_than(inventory_pos)
expect(final_fingerprint_pos).to_be_greater_than(inventory_pos)
expect(equality_pos).to_be_greater_than(final_fingerprint_pos)
expect(build_source).to_contain("if final_symbol_fingerprint != localized_symbol_fingerprint:\n        return llvm_stage4_compiler_backfill_failure(stage_dir, capsule_path, \"Stage4 compiler backfill archive changed the localized symbol table\")")
expect(build_source.substring(0, archive_pos).contains("llvm_stage4_candidate_archive_inventory")).to_be(false)
expect(build_source).to_contain("simple_stage4_compiler_backfill_{{pid}}_{{output_path.hash()}}")
expect(build_source).to_contain("if output_path.trim() == \"\"")
expect(build_source).to_contain("if raw_archive == capsule_path")
expect(build_source).to_contain("dir_remove_all(stage_dir)\n    if dir_exists(stage_dir):\n        return Err(\"Stage4 compiler backfill stale transaction cleanup failed")
expect(build_source).to_contain("var closure_args: [text] = [\"-nostdlib\", \"-Wl,-r\"]")
expect(build_source).to_contain("closure_args = closure_args.push(\"-no-pie\")")
expect(build_source).to_contain("closure_args = closure_args.push(\"-Wl,--gc-sections\")")
expect(build_source).to_contain("for symbol in manifest:\n            closure_args = closure_args.push(\"-Wl,--undefined={{symbol}}\")")
expect(build_source).to_contain("for symbol in manifest:\n            closure_args = closure_args.push(\"-Wl,-u,_{{symbol}}\")")
expect(build_source).to_not_contain("--whole-archive")        expect(build_source).to_not_contain("-force_load")        for flag in [
    "\"--localize-symbols=\" + localize_path,",
    "\"--remove-section=.init_array\",", "\"--remove-section=.init_array.*\",",
    "\"--remove-section=.ctors\",", "\"--remove-section=.ctors.*\",",
    "\"--remove-section=.fini_array\",", "\"--remove-section=.fini_array.*\",",
    "\"--remove-section=.dtors\",", "\"--remove-section=.dtors.*\",",
    "\"--remove-section=__mod_init_func\",", "\"--remove-section=__mod_term_func\",",
    "\"--remove-section=__DATA,__mod_init_func\",", "\"--remove-section=__DATA,__mod_term_func\","
]:
    expect(build_source).to_contain(flag)
expect(build_source.split("\"--remove-section=").len() - 1).to_equal(12)
expect(build_source).to_contain("process_run(archiver, [\"t\", capsule_path])")
expect(build_source).to_not_contain("file_delete(raw_archive)")        expect(build_source).to_not_contain("remove_file_if_exists(raw_archive)")        expect(build_source).to_not_contain("file_copy(raw_archive")        expect(build_source).to_not_contain("file_write(raw_archive")        expect(build_source).to_not_contain("dir_remove_all(raw_archive")
```

</details>

#### owns and cleans the compiler capsule only inside the strict Stage4 transaction

- owns and cleans the compiler capsule only inside the strict Stage4 transaction


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("owns and cleans the compiler capsule only inside the strict Stage4 transaction")
val source = compiler_native_link_source()
val final_symbols_pos = source.find("match llvm_stage4_final_requested_symbols(final_simple_objects)")
val capsule_pos = source.last_index_of("llvm_stage4_build_compiler_backfill_capsule(runtime_path, hosted_os, hosted_cc, pid, output)")
val provider_pos = source.last_index_of("llvm_stage4_build_dynload_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
val projection_pos = source.find("llvm_stage4_project_selected_archives(candidate_labels, candidate_paths, selected_archive_indices, stage4_requested_symbols")
expect(capsule_pos).to_be_greater_than(final_symbols_pos)
expect(provider_pos).to_be_greater_than(capsule_pos)
expect(projection_pos).to_be_greater_than(provider_pos)
expect(source).to_contain("simple_stage4_compiler_backfill_{{pid}}_{{output.hash()}}")
expect(source.split("return llvm_stage4_compiler_backfill_failure(compiler_backfill_stage_dir, compiler_backfill_capsule,").len() - 1).to_be_greater_than(8)
expect(source).to_not_contain("all_objects = all_objects.push(compiler_backfill_capsule)")        expect(source).to_not_contain("link_to_native(all_objects.push(compiler_backfill_capsule)")        val step3_pos = source.find("# Step 3: Combine all objects and link")
expect(step3_pos).to_be_greater_than(projection_pos)
val strict_source = if final_symbols_pos >= 0 and step3_pos > final_symbols_pos: source.substring(final_symbols_pos, step3_pos) else: ""
expect(strict_source).to_contain("compiler_backfill_capsule")
expect(source.substring(step3_pos, source.len()).contains("compiler_backfill_capsule")).to_be(false)
```

</details>

#### inventories runtime-native and capability providers before projection

- inventories runtime-native and capability providers before projection
   - Expected: source.split("llvm_stage4_candidate_archive_inventory(candidate_labels, candidate_paths)").len() - 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("inventories runtime-native and capability providers before projection")
val source = compiler_native_link_source()
val fork_pos = source.last_index_of("llvm_stage4_build_fork_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
val labels_pos = source.find("var candidate_labels = [\"compiler_backfill\", \"runtime_native\", \"runtime_contracts\", \"runtime_legacy_compat\", \"runtime_process\", \"runtime_dynload\", \"runtime_font\", \"runtime_memtrack\", \"runtime_timestamp\"]")
val inventory_pos = source.find("llvm_stage4_candidate_archive_inventory(candidate_labels, candidate_paths)")
val disjoint_pos = source.find("stage4_validate_compiler_backfill_provider_disjoint(candidate_scans[0], candidate_labels[1:], candidate_scans[1:], compiler_backfill_object_format)")
val owner_pos = source.find("stage4_resolve_requested_archive_owners(stage4_requested_symbols, candidate_labels, candidate_scans, hosted_os == \"macos\")")
val projection_pos = source.find("llvm_stage4_project_selected_archives(candidate_labels, candidate_paths, selected_archive_indices, stage4_requested_symbols")
val step3_pos = source.find("# Step 3: Combine all objects and link")
expect(labels_pos).to_be_greater_than(fork_pos)
expect(inventory_pos).to_be_greater_than(labels_pos)
expect(disjoint_pos).to_be_greater_than(inventory_pos)
expect(owner_pos).to_be_greater_than(disjoint_pos)
expect(projection_pos).to_be_greater_than(owner_pos)
expect(step3_pos).to_be_greater_than(projection_pos)
expect(source).to_contain("var candidate_paths = [compiler_backfill_capsule, runtime_native_archive, contracts_provider_archive, runtime_legacy_compat_archive, process_provider_archive, dynload_provider_archive, font_provider_archive, memtrack_provider_archive, time_provider_archive]")
expect(source.split("llvm_stage4_candidate_archive_inventory(candidate_labels, candidate_paths)").len() - 1).to_equal(1)
val strict_source = if labels_pos >= 0 and step3_pos > labels_pos: source.substring(labels_pos, step3_pos) else: ""
expect(strict_source).to_contain("for path in candidate_paths:")
expect(strict_source).to_contain("remove_file_if_exists(path)")
```

</details>

#### builds and validates the dedicated dynload archive before strict projection

- builds and validates the dedicated dynload archive before strict projection
   - Expected: source).to_not_contain("_obj_ext() == \".obj\"")        expect(source.split("stage4_msvc_objects, stage4_msvc_linker, pid").len() - 1 equals `8`
   - Expected: source.split("archive_file, object_ext, target_os_name == \"windows\", pid").len() - 1 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds and validates the dedicated dynload archive before strict projection")
val source = compiler_native_link_source()
val inventory_pos = source.find("fn llvm_stage4_candidate_archive_inventory")
val config_pos = source.find("# Configuration")
expect(inventory_pos).to_be_greater_than(-1)
expect(config_pos).to_be_greater_than(inventory_pos)
val inventory_source = source.substring(inventory_pos, config_pos)
val validate_pos = inventory_source.find("stage4_validate_candidate_archive_inputs_for_platform(")
val exists_pos = inventory_source.find("file_exists(")
val resolver_pos = inventory_source.find("find_nm_portable()")
val section_resolver_pos = inventory_source.find("find_objdump_portable()")
val section_scan_pos = inventory_source.find("process_run(section_reader")
val forbidden_pos = inventory_source.find("stage4_forbidden_archive_sections(section_out)")
val scan_pos = inventory_source.find("process_run(nm")
expect(validate_pos).to_be_greater_than(-1)
expect(resolver_pos).to_be_greater_than(validate_pos)
expect(section_resolver_pos).to_be_greater_than(resolver_pos)
expect(exists_pos).to_be_greater_than(validate_pos)
expect(section_scan_pos).to_be_greater_than(exists_pos)
expect(forbidden_pos).to_be_greater_than(section_scan_pos)
expect(scan_pos).to_be_greater_than(resolver_pos)
expect(scan_pos).to_be_greater_than(forbidden_pos)
expect(inventory_source).to_contain("section scan failed")
expect(inventory_source).to_contain("section scan was empty")
expect(inventory_source).to_contain("retained constructor/destructor sections")
expect(inventory_source).to_contain("stage4_validate_candidate_archive_inputs_for_platform(labels, paths, host_os() == \"windows\")")
val build_pos = source.find("fn llvm_stage4_build_single_object_provider_archive")
val production_pos = source.last_index_of("llvm_stage4_build_dynload_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
val projection_pos = source.find("llvm_stage4_project_selected_archives(candidate_labels, candidate_paths, selected_archive_indices, stage4_requested_symbols")
val step3_pos = source.find("# Step 3: Combine all objects and link")
val build_source = source.substring(build_pos, source.find("# Configuration"))
val copy_pos = build_source.find("file_copy(provider_objects[0], staged_object)")
val archive_pos = build_source.find("process_run(archiver, [\"rcsD\", archive_path, staged_object])")
val list_pos = build_source.find("process_run(archiver, [\"t\", archive_path])")
val inventory_call_pos = build_source.find("llvm_stage4_candidate_archive_inventory([\"runtime_dynload\"], [archive_path])")
val contract_pos = build_source.find("stage4_validate_dynload_provider_symbol_contract(scans[0], object_format)")
expect(build_pos).to_be_greater_than(inventory_pos)
expect(production_pos).to_be_greater_than(build_pos)
expect(projection_pos).to_be_greater_than(production_pos)
expect(step3_pos).to_be_greater_than(projection_pos)
expect(copy_pos).to_be_greater_than(-1)
expect(archive_pos).to_be_greater_than(copy_pos)
expect(list_pos).to_be_greater_than(archive_pos)
expect(inventory_call_pos).to_be_greater_than(list_pos)
expect(contract_pos).to_be_greater_than(inventory_call_pos)
expect(source).to_contain("find_archive_portable()")
expect(source).to_contain("stage4_runtime_provider_object_matches(object, object_stem, object_ext, windows_paths)")
expect(source).to_not_contain("_obj_ext() == \".obj\"")        expect(source.split("stage4_msvc_objects, stage4_msvc_linker, pid").len() - 1).to_equal(8)
expect(source.split("archive_file, object_ext, target_os_name == \"windows\", pid").len() - 1).to_equal(6)
expect(source).to_contain("compile_entry_point_c(user_objects, pid, verbose, options.opt_level, hosted_cc)")
expect(source).to_not_contain("object.ends_with(object_stem + object_ext)")        expect(source).to_contain("provider_objects.len() != 1")
expect(source).to_contain("file_copy(provider_objects[0], staged_object)")
expect(source).to_contain("val expected_member = object_stem + object_ext")
expect(source).to_contain("llvm_stage4_build_single_object_provider_archive(runtime_objects, \"runtime_dynload\"")
expect(source).to_contain("process_run(archiver, [\"rcsD\", archive_path, staged_object])")
expect(source).to_contain("process_run(archiver, [\"t\", archive_path])")
expect(source).to_contain("members_out.replace(\"\\r\", \"\").trim()")
expect(source).to_contain("llvm_stage4_candidate_archive_inventory([\"runtime_dynload\"], [archive_path])")
expect(source).to_contain("stage4_validate_dynload_provider_symbol_contract(scans[0], object_format)")
expect(source).to_contain("dir_remove_all(stage_dir)")
expect(source).to_not_contain("runtime_dynload.c")
```

</details>

#### routes both Stage4 symbol scans through the portable nm resolver

- routes both Stage4 symbol scans through the portable nm resolver
   - Expected: inventory_source.split("section_err.trim() != \"\"").len() - 1 equals `1`
   - Expected: source.split("process_run(\"nm\"").len() - 1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes both Stage4 symbol scans through the portable nm resolver")
val source = compiler_native_link_source()
val final_pos = source.find("fn llvm_stage4_final_requested_symbols")
val inventory_pos = source.find("fn llvm_stage4_candidate_archive_inventory")
val config_pos = source.find("# Configuration")
val final_source = source.substring(final_pos, inventory_pos)
val inventory_source = source.substring(inventory_pos, config_pos)
val section_exit_pos = inventory_source.find("if section_code != 0")
val section_diagnostic_pos = inventory_source.find("if section_err.trim() != \"\"")
val forbidden_pos = inventory_source.find("stage4_forbidden_archive_sections(section_out)")
expect(final_source).to_contain("find_nm_portable()")
expect(final_source).to_contain("process_run(nm, args)")
expect(inventory_source).to_contain("find_nm_portable()")
expect(inventory_source).to_contain("process_run(nm, [\"-g\", path])")
expect(section_diagnostic_pos).to_be_greater_than(section_exit_pos)
expect(forbidden_pos).to_be_greater_than(section_diagnostic_pos)
expect(inventory_source.split("section_err.trim() != \"\"").len() - 1).to_equal(1)
expect(source).to_contain("diagnostics despite exit 0")
expect(source.split("process_run(\"nm\"").len() - 1).to_equal(0)
```

</details>

#### keeps the portable nm override and LLVM-first fallback order

- keeps the portable nm override and LLVM-first fallback order


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the portable nm override and LLVM-first fallback order")
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_capability.spl") ?? ""
val resolver_pos = source.find("pub fn find_nm_portable")
val detect_pos = source.find("# Detect libLLVM availability")
val resolver_source = source.substring(resolver_pos, detect_pos)
val override_pos = resolver_source.find("env_get(\"SIMPLE_NM\")")
val newest_pos = resolver_source.find("\"llvm-nm-22\"")
val fallback_pos = resolver_source.find("\"nm\"")
expect(override_pos).to_be_greater_than(-1)
expect(newest_pos).to_be_greater_than(override_pos)
expect(fallback_pos).to_be_greater_than(newest_pos)
expect(source).to_contain("for path in out.split(\"\\n\")")
```

</details>

#### keeps the deterministic archiver override and ar-compatible fallbacks

- keeps the deterministic archiver override and ar-compatible fallbacks


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the deterministic archiver override and ar-compatible fallbacks")
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_capability.spl") ?? ""
val resolver_pos = source.find("pub fn find_archive_portable")
val next_pos = source.find("pub fn find_objdump_portable")
val resolver_source = source.substring(resolver_pos, next_pos)
val override_pos = resolver_source.find("env_get(\"SIMPLE_AR\")")
val newest_pos = resolver_source.find("\"llvm-ar-22\"")
val fallback_pos = resolver_source.last_index_of("\"ar\"")
expect(override_pos).to_be_greater_than(-1)
expect(newest_pos).to_be_greater_than(override_pos)
expect(fallback_pos).to_be_greater_than(newest_pos)
expect(resolver_source).to_not_contain("\"lib\"")
```

</details>

#### keeps the portable section-reader override and platform-safe fallbacks

- keeps the portable section-reader override and platform-safe fallbacks


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the portable section-reader override and platform-safe fallbacks")
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_capability.spl") ?? ""
val resolver_pos = source.find("pub fn find_objdump_portable")
val detect_pos = source.find("# Detect libLLVM availability")
val resolver_source = source.substring(resolver_pos, detect_pos)
val override_pos = resolver_source.find("env_get(\"SIMPLE_OBJDUMP\")")
val newest_pos = resolver_source.last_index_of("\"llvm-objdump-22\"")
val readelf_pos = resolver_source.last_index_of("\"readelf\"")
val fallback_pos = resolver_source.last_index_of("\"objdump\"")
expect(override_pos).to_be_greater_than(-1)
expect(newest_pos).to_be_greater_than(override_pos)
expect(readelf_pos).to_be_greater_than(newest_pos)
expect(fallback_pos).to_be_greater_than(readelf_pos)
expect(resolver_source).to_contain("/opt/homebrew/opt/llvm/bin/llvm-objdump")
```

</details>

#### keeps the portable objcopy override and LLVM-first discovery order

- keeps the portable objcopy override and LLVM-first discovery order


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the portable objcopy override and LLVM-first discovery order")
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_capability.spl") ?? ""
val resolver_pos = source.find("pub fn find_objcopy_portable")
val detect_pos = source.find("# Detect libLLVM availability")
val resolver_source = source.substring(resolver_pos, detect_pos)
val override_pos = resolver_source.find("env_get(\"SIMPLE_OBJCOPY\")")
val discovery_pos = resolver_source.find("find_tool_portable([")
val newest_pos = resolver_source.find("\"llvm-objcopy-22\"")
val llvm_pos = resolver_source.last_index_of("\"llvm-objcopy\"")
val fallback_pos = resolver_source.last_index_of("\"objcopy\"")
val opt_18_pos = resolver_source.find("/opt/homebrew/opt/llvm@18/bin/llvm-objcopy")
val opt_pos = resolver_source.find("/opt/homebrew/opt/llvm/bin/llvm-objcopy")
val usr_18_pos = resolver_source.find("/usr/local/opt/llvm@18/bin/llvm-objcopy")
val usr_pos = resolver_source.find("/usr/local/opt/llvm/bin/llvm-objcopy")
expect(resolver_pos).to_be_greater_than(-1)
expect(override_pos).to_be_greater_than(-1)
expect(discovery_pos).to_be_greater_than(override_pos)
expect(newest_pos).to_be_greater_than(discovery_pos)
expect(llvm_pos).to_be_greater_than(newest_pos)
expect(fallback_pos).to_be_greater_than(llvm_pos)
expect(opt_18_pos).to_be_greater_than(discovery_pos)
expect(opt_pos).to_be_greater_than(opt_18_pos)
expect(usr_18_pos).to_be_greater_than(opt_pos)
expect(usr_pos).to_be_greater_than(usr_18_pos)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fae6e23e831412fbd7884a11f25ac6ecf3be2f05ff1925a74e4dd409bd1e9928`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fae6e23e831412fbd7884a11f25ac6ecf3be2f05ff1925a74e4dd409bd1e9928`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fae6e23e831412fbd7884a11f25ac6ecf3be2f05ff1925a74e4dd409bd1e9928`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/stage4_native_link_source_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers the canonical native-all archive name for each hosted OS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a private deterministic compiler backfill capsule from the derived manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_native_link_source_contract_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns and cleans the compiler capsule only inside the strict Stage4 transaction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
