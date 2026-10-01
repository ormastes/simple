# Contract spec: test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl` |
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
`bin/simple test test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl` and a green Results line.

## Scenarios

### Stage4 aggregate final symbol closure

#### matches provider objects only at a portable leaf token boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches provider objects only at a portable leaf token boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches provider objects only at a portable leaf token boundary")
expect(stage4_runtime_provider_object_matches("/tmp/simple_rt_7_x86_64-linux-gnu_runtime_font.o", "runtime_font", ".o", false)).to_be(true)
expect(stage4_runtime_provider_object_matches("/tmp/runtime_font.o", "runtime_font", ".o", false)).to_be(true)
expect(stage4_runtime_provider_object_matches("C:\\Temp\\SIMPLE_RT_7_HOST_RUNTIME_FONT.OBJ", "runtime_font", ".obj", true)).to_be(true)
expect(stage4_runtime_provider_object_matches("C:\\Temp\\SIMPLE_RT_7_HOST_RUNTIME_FONT.O", "runtime_font", ".o", true)).to_be(true)
expect(stage4_runtime_provider_object_matches("/tmp/notruntime_font.o", "runtime_font", ".o", false)).to_be(false)
expect(stage4_runtime_provider_object_matches("/tmp/runtime_font.o.bak", "runtime_font", ".o", false)).to_be(false)
expect(stage4_runtime_provider_object_matches("/tmp/RUNTIME_FONT.O", "runtime_font", ".o", false)).to_be(false)
expect(stage4_runtime_provider_object_matches("/tmp/runtime_font.o/leaf", "runtime_font", ".o", false)).to_be(false)
expect(stage4_runtime_provider_object_matches("", "runtime_font", ".o", false)).to_be(false)
```

</details>

#### names and localizes the runtime-native archive for each hosted object ABI

- names and localizes the runtime-native archive for each hosted object ABI
   - Expected: stage4_runtime_native_archive_file("linux", false).unwrap() equals `libsimple_stage4_runtime_native.a`
   - Expected: stage4_runtime_native_archive_file("macos", false).unwrap() equals `libsimple_stage4_runtime_native.a`
   - Expected: stage4_runtime_native_archive_file("freebsd", false).unwrap() equals `libsimple_stage4_runtime_native.a`
   - Expected: stage4_runtime_native_archive_file("windows", false).unwrap() equals `libsimple_stage4_runtime_native.a`
   - Expected: stage4_runtime_native_archive_file("windows", true).unwrap() equals `simple_stage4_runtime_native.lib`
   - Expected: stage4_runtime_native_object_format("linux", false).unwrap() equals `elf`
   - Expected: stage4_runtime_native_object_format("freebsd", false).unwrap() equals `elf`
   - Expected: stage4_runtime_native_object_format("macos", false).unwrap() equals `macho`
   - Expected: stage4_runtime_native_object_format("windows", false).unwrap() equals `coff-mingw`
   - Expected: stage4_runtime_native_object_format("windows", true).unwrap() equals `coff-msvc`
   - Expected: stage4_runtime_native_localization_symbols(required + legacy, "elf").unwrap() equals `["spl_dlclose", "spl_dlopen", "spl_dlsym"]`
   - Expected: stage4_runtime_native_localization_symbols(required + legacy.replace("0011 T spl_dlsym\n", ""), "elf").unwrap() equals `["spl_dlclose", "spl_dlopen"]`
   - Expected: stage4_runtime_native_localization_symbols(required, "elf").unwrap() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names and localizes the runtime-native archive for each hosted object ABI")
expect(stage4_runtime_native_archive_file("linux", false).unwrap()).to_equal("libsimple_stage4_runtime_native.a")
expect(stage4_runtime_native_archive_file("macos", false).unwrap()).to_equal("libsimple_stage4_runtime_native.a")
expect(stage4_runtime_native_archive_file("freebsd", false).unwrap()).to_equal("libsimple_stage4_runtime_native.a")
expect(stage4_runtime_native_archive_file("windows", false).unwrap()).to_equal("libsimple_stage4_runtime_native.a")
expect(stage4_runtime_native_archive_file("windows", true).unwrap()).to_equal("simple_stage4_runtime_native.lib")
expect(stage4_runtime_native_archive_file("linux", true).is_err()).to_be(true)
expect(stage4_runtime_native_archive_file("plan9", false).is_err()).to_be(true)
expect(stage4_runtime_native_object_format("linux", false).unwrap()).to_equal("elf")
expect(stage4_runtime_native_object_format("freebsd", false).unwrap()).to_equal("elf")
expect(stage4_runtime_native_object_format("macos", false).unwrap()).to_equal("macho")
expect(stage4_runtime_native_object_format("windows", false).unwrap()).to_equal("coff-mingw")
expect(stage4_runtime_native_object_format("windows", true).unwrap()).to_equal("coff-msvc")
expect(stage4_runtime_native_object_format("linux", true).is_err()).to_be(true)
expect(stage4_runtime_native_object_format("plan9", false).is_err()).to_be(true)

val required = "0001 T rt_http_download\n0002 T rt_http_get\n0003 T rt_http_request\n0004 T rt_interp_cstr\n0005 T rt_string_data\n0006 T rt_string_new\n0007 T rt_time_now_nanos\n0008 T rt_time_now_unix_micros\n"
val legacy = "0009 T spl_dlclose\n0010 T spl_dlopen\n0011 T spl_dlsym\n"
expect(stage4_runtime_native_localization_symbols(required + legacy, "elf").unwrap()).to_equal(["spl_dlclose", "spl_dlopen", "spl_dlsym"])
# An ABSENT legacy dynload definition is now the EXPECTED steady state:
# runtime_native.c guards its fallback copies behind
# SIMPLE_RUNTIME_DYNLOAD_OWNER, which runtime_compiler.spl defines on
# every bundle that also compiles runtime_dynload.c (Stage4 always
# does). Nothing to localize is success, not failure.
expect(stage4_runtime_native_localization_symbols(required + legacy.replace("0011 T spl_dlsym\n", ""), "elf").unwrap()).to_equal(["spl_dlclose", "spl_dlopen"])
expect(stage4_runtime_native_localization_symbols(required, "elf").unwrap()).to_equal([])
# A DOUBLE definition is still an error -- that is the shape that would
# put two divergent bodies in one archive core.
expect(stage4_runtime_native_localization_symbols(required + legacy + "0012 T spl_dlopen\n", "elf").is_err()).to_be(true)
expect(stage4_validate_runtime_native_core_symbol_contract(required, "elf").is_ok()).to_be(true)
for missing in ["0001 T rt_http_download\n", "0002 T rt_http_get\n", "0003 T rt_http_request\n"]:
    expect(stage4_runtime_native_localization_symbols(required.replace(missing, "") + legacy, "elf").is_err()).to_be(true)
    expect(stage4_validate_runtime_native_core_symbol_contract(required.replace(missing, ""), "elf").is_err()).to_be(true)
expect(stage4_validate_runtime_native_core_symbol_contract(required + legacy, "elf").is_err()).to_be(true)
expect(stage4_validate_runtime_native_core_symbol_contract(required, "wasm").is_err()).to_be(true)
```

</details>

#### stages runtime core before owner resolution and includes fork only on POSIX

- stages runtime core before owner resolution and includes fork only on POSIX


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stages runtime core before owner resolution and includes fork only on POSIX")
val source = compiler_native_link_source()
val strict_start: i64 = source.find("if stage4_requested:")
val strict_end: i64 = source.find("# Step 3: Combine all objects and link")
val strict_source = if strict_start >= 0 and strict_end > strict_start: source.substring(strict_start, strict_end) else: ""
val core_pos: i64 = strict_source.find("llvm_stage4_build_runtime_native_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
val inventory_pos: i64 = strict_source.find("llvm_stage4_candidate_archive_inventory(candidate_labels, candidate_paths)")
val resolve_pos: i64 = strict_source.find("stage4_resolve_requested_archive_owners(stage4_requested_symbols, candidate_labels, candidate_scans, hosted_os == \"macos\")")
val fork_guard_pos: i64 = strict_source.find("if hosted_os != \"windows\":")
val fork_build_pos: i64 = strict_source.find("llvm_stage4_build_fork_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
val fork_candidate_guard_pos: i64 = strict_source.find("if fork_provider_archive != \"\":")
val fork_candidate_pos: i64 = strict_source.find("candidate_labels = candidate_labels.push(\"runtime_fork\")")
expect(strict_start).to_be_greater_than(-1)
expect(strict_end).to_be_greater_than(strict_start)
expect(core_pos).to_be_greater_than(-1)
expect(inventory_pos).to_be_greater_than(core_pos)
expect(resolve_pos).to_be_greater_than(inventory_pos)
expect(strict_source).to_contain("\"runtime_native\"")
expect(fork_guard_pos).to_be_greater_than(-1)
expect(fork_build_pos).to_be_greater_than(fork_guard_pos)
expect(fork_candidate_guard_pos).to_be_greater_than(fork_build_pos)
expect(fork_candidate_pos).to_be_greater_than(fork_candidate_guard_pos)
```

</details>

#### rejects emit-object before Stage4 can bypass the strict linker

- rejects emit-object before Stage4 can bypass the strict linker


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects emit-object before Stage4 can bypass the strict linker")
val source = rt_file_read_text(
    "src/compiler/80.driver/driver_aot_native_output.spl") ?? ""
val guard_pos = source.find("if stage4_requested and emit_object_requested:")
val cache_pos = source.find("# Load build cache")
val output_source = source.substring(cache_pos)
expect(guard_pos).to_be_greater_than(-1)
expect(cache_pos).to_be_greater_than(guard_pos)
expect(output_source.find("if emit_object_requested:")).to_be_greater_than(-1)
expect(source).to_contain("Stage4 strict profile does not support emit-object output")
```

</details>

#### uses seed-safe canonical ordering instead of the seed no-op sort

- uses seed-safe canonical ordering instead of the seed no-op sort


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses seed-safe canonical ordering instead of the seed no-op sort")
val source = rt_file_read_text("src/compiler/70.backend/backend/stage4_symbol_closure.spl") ?? ""
expect(source).to_contain("fn stage4_sorted_text")
expect(source).to_not_contain(".sort()")
```

</details>

#### names compiler backfill capsules only on supported native hosts

- names compiler backfill capsules only on supported native hosts
   - Expected: stage4_compiler_backfill_archive_file("linux").unwrap() equals `libsimple_compiler_backfill.a`
   - Expected: stage4_compiler_backfill_archive_file("macos").unwrap() equals `libsimple_compiler_backfill.a`
   - Expected: stage4_compiler_backfill_object_format("linux").unwrap() equals `elf`
   - Expected: stage4_compiler_backfill_object_format("macos").unwrap() equals `macho`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names compiler backfill capsules only on supported native hosts")
expect(stage4_compiler_backfill_archive_file("linux").unwrap()).to_equal("libsimple_compiler_backfill.a")
expect(stage4_compiler_backfill_archive_file("macos").unwrap()).to_equal("libsimple_compiler_backfill.a")
expect(stage4_compiler_backfill_object_format("linux").unwrap()).to_equal("elf")
expect(stage4_compiler_backfill_object_format("macos").unwrap()).to_equal("macho")
expect(stage4_compiler_backfill_archive_file("windows").is_err()).to_be(true)
expect(stage4_compiler_backfill_archive_file("freebsd").is_err()).to_be(true)
expect(stage4_compiler_backfill_archive_file("plan9").is_err()).to_be(true)
expect(stage4_compiler_backfill_object_format("windows").is_err()).to_be(true)
expect(stage4_compiler_backfill_object_format("freebsd").is_err()).to_be(true)
expect(stage4_compiler_backfill_object_format("plan9").is_err()).to_be(true)
```

</details>

#### accepts compiler backfill symbol envelopes for ELF and Mach-O

- accepts compiler backfill symbol envelopes for ELF and Mach-O


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts compiler backfill symbol envelopes for ELF and Mach-O")
val elf = "0000000000000000 T rt_cranelift_new_module\n0000000000000010 T rt_cranelift_emit_object_raw\n                 U malloc\n"
val macho = "0000000000000000 T _rt_cranelift_new_module\n0000000000000010 T _rt_cranelift_emit_object_raw\n                 U _malloc\n"
expect(stage4_validate_compiler_backfill_symbol_envelope(elf, "elf").is_ok()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(macho, "macho").is_ok()).to_be(true)
```

</details>

#### derives sorted compiler backfill manifests and preserves raw localization names

- derives sorted compiler backfill manifests and preserves raw localization names
   - Expected: stage4_derive_compiler_backfill_manifest(elf, "elf").unwrap() equals `expected`
   - Expected: stage4_derive_compiler_backfill_manifest(macho, "macho").unwrap() equals `expected`
   - Expected: stage4_compiler_backfill_localization_symbols(elf, "elf", expected).unwrap() equals `["helper_a", "helper_z"]`
   - Expected: stage4_compiler_backfill_localization_symbols(macho, "macho", expected).unwrap() equals `["_helper_a", "_helper_z"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("derives sorted compiler backfill manifests and preserves raw localization names")
val elf = "T rt_cranelift_zeta\n00000010 T helper_z\n00000020 T rt_cranelift_alpha\n00000030 T helper_a\n"
val macho = "T _rt_cranelift_zeta\n00000010 T _helper_z\n00000020 T _rt_cranelift_alpha\n00000030 T _helper_a\n"
val expected = ["rt_cranelift_alpha", "rt_cranelift_zeta"]
expect(stage4_derive_compiler_backfill_manifest(elf, "elf").unwrap()).to_equal(expected)
expect(stage4_derive_compiler_backfill_manifest(macho, "macho").unwrap()).to_equal(expected)
expect(stage4_compiler_backfill_localization_symbols(elf, "elf", expected).unwrap()).to_equal(["helper_a", "helper_z"])
expect(stage4_compiler_backfill_localization_symbols(macho, "macho", expected).unwrap()).to_equal(["_helper_a", "_helper_z"])
```

</details>

#### rejects empty repeated and foreign runtime compiler manifests

- rejects empty repeated and foreign runtime compiler manifests


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects empty repeated and foreign runtime compiler manifests")
val export = "00000000 T rt_cranelift_compile\n"
expect(stage4_derive_compiler_backfill_manifest("", "elf").unwrap_err()).to_contain("defines no rt_cranelift")
expect(stage4_derive_compiler_backfill_manifest("00000000 T helper\n", "elf").unwrap_err()).to_contain("defines no rt_cranelift")
expect(stage4_derive_compiler_backfill_manifest(export + export, "elf").unwrap_err()).to_contain("exactly once")
expect(stage4_derive_compiler_backfill_manifest(export + "00000010 T rt_hidden\n00000020 T spl_hidden\n", "elf").unwrap_err()).to_contain("outside the manifest")
expect(stage4_derive_compiler_backfill_manifest(export + "U rt_hidden\nU spl_hidden\n", "elf").unwrap_err()).to_contain("outside the manifest")
expect(stage4_derive_compiler_backfill_manifest("00000000 T rt_cranelift_noise extra\n", "elf").unwrap_err()).to_contain("defines no rt_cranelift")
```

</details>

#### requires each localization manifest export exactly once

- requires each localization manifest export exactly once


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("requires each localization manifest export exactly once")
val exact = "00000000 T rt_cranelift_compile\n00000010 T helper\n"
expect(stage4_compiler_backfill_localization_symbols(exact, "elf", []).unwrap_err()).to_contain("manifest is empty")
expect(stage4_compiler_backfill_localization_symbols(exact, "elf", ["rt_cranelift_compile", "rt_cranelift_compile"]).unwrap_err()).to_contain("repeats export")
expect(stage4_compiler_backfill_localization_symbols("00000010 T helper\n", "elf", ["rt_cranelift_compile"]).unwrap_err()).to_contain("exactly once")
expect(stage4_compiler_backfill_localization_symbols(exact + "00000020 T rt_cranelift_compile\n", "elf", ["rt_cranelift_compile"]).unwrap_err()).to_contain("exactly once")
```

</details>

#### rejects strong and weak runtime dependencies before localization

- rejects strong and weak runtime dependencies before localization


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects strong and weak runtime dependencies before localization")
val exact = "00000000 T rt_cranelift_compile\n"
expect(stage4_compiler_backfill_localization_symbols(exact + "U rt_hidden\n", "elf", ["rt_cranelift_compile"]).unwrap_err()).to_contain("forbidden runtime dependency")
expect(stage4_compiler_backfill_localization_symbols(exact + "00000010 w spl_weak\n", "elf", ["rt_cranelift_compile"]).unwrap_err()).to_contain("forbidden runtime dependency")
```

</details>

#### rejects invalid compiler backfill symbol envelopes

- rejects invalid compiler backfill symbol envelopes


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects invalid compiler backfill symbol envelopes")
val exact = "0000000000000000 T rt_cranelift_new_module\n0000000000000010 T rt_cranelift_emit_object_raw\n"
expect(stage4_validate_compiler_backfill_symbol_envelope("", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact + "0000000000000020 T rt_cranelift_new_module\n", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact + "0000000000000020 T compiler_helper\n", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact + "0000000000000020 T rt_cranelift_module_new\n", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact + "0000000000000020 T rt_cranelift_emit_object\n", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact + "                 U rt_hidden_dependency\n", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact + "                 U spl_hidden_dependency\n", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact + "                 w rt_weak_dependency\n", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact + "                 v spl_weak_dependency\n", "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_symbol_envelope(exact, "coff-msvc").is_err()).to_be(true)
```

</details>

#### fingerprints the exact raw compiler backfill symbol table deterministically

- fingerprints the exact raw compiler backfill symbol table deterministically
   - Expected: stage4_compiler_backfill_symbol_table_fingerprint(rows).unwrap() equals `expected`
   - Expected: stage4_compiler_backfill_symbol_table_fingerprint(permuted).unwrap() equals `expected`
   - Expected: stage4_compiler_backfill_symbol_table_fingerprint("00000000 T shared\n         U shared\n").unwrap() equals `defined\t1\tshared\nundefined\tshared`
   - Expected: stage4_compiler_backfill_symbol_table_fingerprint("00000000 T _raw\n").unwrap() equals `defined\t1\t_raw`
   - Expected: stage4_compiler_backfill_symbol_table_fingerprint("00000000 T raw\n").unwrap() equals `defined\t1\traw`
   - Expected: stage4_compiler_backfill_symbol_table_fingerprint("").unwrap() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fingerprints the exact raw compiler backfill symbol table deterministically")
val rows = "         v _malloc\n00000030 T _rt_cranelift_zeta\n00000010 T _rt_cranelift_alpha\n         U _malloc\n00000020 T _rt_cranelift_zeta\n         w _malloc\n00000040 T ignored extra\n"
val permuted = "00000020 T _rt_cranelift_zeta\n         w _malloc\n00000010 T _rt_cranelift_alpha\n         U _malloc\n00000030 T _rt_cranelift_zeta\n         v _malloc\n"
val expected = "defined\t1\t_rt_cranelift_alpha\ndefined\t2\t_rt_cranelift_zeta\nundefined\t_malloc"
expect(stage4_compiler_backfill_symbol_table_fingerprint(rows).unwrap()).to_equal(expected)
expect(stage4_compiler_backfill_symbol_table_fingerprint(permuted).unwrap()).to_equal(expected)
expect(stage4_compiler_backfill_symbol_table_fingerprint("00000000 T shared\n         U shared\n").unwrap()).to_equal("defined\t1\tshared\nundefined\tshared")
expect(stage4_compiler_backfill_symbol_table_fingerprint("00000000 T _raw\n").unwrap()).to_equal("defined\t1\t_raw")
expect(stage4_compiler_backfill_symbol_table_fingerprint("00000000 T raw\n").unwrap()).to_equal("defined\t1\traw")
expect(stage4_compiler_backfill_symbol_table_fingerprint("").unwrap()).to_equal("")
```

</details>

#### requires the compiler capsule and providers to have disjoint canonical definitions

- requires the compiler capsule and providers to have disjoint canonical definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("requires the compiler capsule and providers to have disjoint canonical definitions")
val elf_capsule = "00000000 T rt_cranelift_compile\n         U malloc\n"
val elf_providers = ["00000000 T rt_font_load\n", "00000000 T spl_memtrack_enable\n"]
val macho_capsule = "00000000 T _rt_cranelift_compile\n         U _malloc\n"
val macho_providers = ["00000000 T _rt_font_load\n", "00000000 T _spl_memtrack_enable\n"]
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, ["font", "memtrack"], elf_providers, "elf").is_ok()).to_be(true)
expect(stage4_validate_compiler_backfill_provider_disjoint(macho_capsule, ["font", "memtrack"], macho_providers, "macho").is_ok()).to_be(true)
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, [], [], "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, ["font"], [], "elf").is_err()).to_be(true)
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, [""], [elf_providers[0]], "elf").unwrap_err()).to_contain("provider label is empty")
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, ["font", "font"], elf_providers, "elf").unwrap_err()).to_contain("provider label 'font' is repeated")
expect(stage4_validate_compiler_backfill_provider_disjoint("         U malloc\n", ["font"], [elf_providers[0]], "elf").unwrap_err()).to_contain("capsule defines no global symbols")
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, ["font"], ["         U malloc\n"], "elf").unwrap_err()).to_contain("provider 'font' defines no global symbols")
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, ["font"], ["00000000 T rt_cranelift_compile\n"], "elf").unwrap_err()).to_contain("overlaps provider 'font': rt_cranelift_compile")
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, ["font", "compiler"], [elf_providers[0], "00000000 T rt_cranelift_compile\n"], "elf").unwrap_err()).to_contain("overlaps provider 'compiler': rt_cranelift_compile")
expect(stage4_validate_compiler_backfill_provider_disjoint(macho_capsule, ["font"], ["00000000 T rt_cranelift_compile\n"], "macho").unwrap_err()).to_contain("overlaps provider 'font': rt_cranelift_compile")
expect(stage4_validate_compiler_backfill_provider_disjoint(elf_capsule, ["font"], [elf_providers[0]], "coff-msvc").is_err()).to_be(true)
```

</details>

#### defines target-explicit dynamic-loader archive identities without building them

- defines target-explicit dynamic-loader archive identities without building them
   - Expected: stage4_dynload_provider_archive_file("linux", false).unwrap() equals `libsimple_stage4_dynload.a`
   - Expected: stage4_dynload_provider_archive_file("macos", false).unwrap() equals `libsimple_stage4_dynload.a`
   - Expected: stage4_dynload_provider_archive_file("freebsd", false).unwrap() equals `libsimple_stage4_dynload.a`
   - Expected: stage4_dynload_provider_archive_file("windows", false).unwrap() equals `libsimple_stage4_dynload.a`
   - Expected: stage4_dynload_provider_archive_file("windows", true).unwrap() equals `simple_stage4_dynload.lib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("defines target-explicit dynamic-loader archive identities without building them")
expect(stage4_dynload_provider_archive_file("linux", false).unwrap()).to_equal("libsimple_stage4_dynload.a")
expect(stage4_dynload_provider_archive_file("macos", false).unwrap()).to_equal("libsimple_stage4_dynload.a")
expect(stage4_dynload_provider_archive_file("freebsd", false).unwrap()).to_equal("libsimple_stage4_dynload.a")
expect(stage4_dynload_provider_archive_file("windows", false).unwrap()).to_equal("libsimple_stage4_dynload.a")
expect(stage4_dynload_provider_archive_file("windows", true).unwrap()).to_equal("simple_stage4_dynload.lib")
expect(stage4_dynload_provider_archive_file("linux", true).is_err()).to_be(true)
expect(stage4_dynload_provider_archive_file("plan9", false).is_err()).to_be(true)
```

</details>

#### maps hosted dynamic-loader objects to exact portable nm contracts

- maps hosted dynamic-loader objects to exact portable nm contracts
   - Expected: stage4_dynload_provider_object_format("linux", false).unwrap() equals `elf`
   - Expected: stage4_dynload_provider_object_format("freebsd", false).unwrap() equals `elf`
   - Expected: stage4_dynload_provider_object_format("macos", false).unwrap() equals `macho`
   - Expected: stage4_dynload_provider_object_format("windows", false).unwrap() equals `coff-mingw`
   - Expected: stage4_dynload_provider_object_format("windows", true).unwrap() equals `coff-msvc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps hosted dynamic-loader objects to exact portable nm contracts")
expect(stage4_dynload_provider_object_format("linux", false).unwrap()).to_equal("elf")
expect(stage4_dynload_provider_object_format("freebsd", false).unwrap()).to_equal("elf")
expect(stage4_dynload_provider_object_format("macos", false).unwrap()).to_equal("macho")
expect(stage4_dynload_provider_object_format("windows", false).unwrap()).to_equal("coff-mingw")
expect(stage4_dynload_provider_object_format("windows", true).unwrap()).to_equal("coff-msvc")
expect(stage4_dynload_provider_object_format("linux", true).is_err()).to_be(true)
expect(stage4_dynload_provider_object_format("plan9", false).is_err()).to_be(true)
```

</details>

#### derives Windows object ABI from the selected C driver and linker contract

- derives Windows object ABI from the selected C driver and linker contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("derives Windows object ABI from the selected C driver and linker contract")
expect(stage4_windows_c_object_uses_msvc_abi("linux", "host", "/usr/bin/clang", false).unwrap()).to_be(false)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "host", "cl.exe", true).unwrap()).to_be(true)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "x86_64-pc-windows-msvc", "C:/LLVM/BIN/CLANG-CL.EXE", true).unwrap()).to_be(true)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "host", "C:\\mingw64\\bin\\gcc.exe", false).unwrap()).to_be(false)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "x64", "x86_64-w64-mingw32-gcc", false).unwrap()).to_be(false)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "host", "clang.exe", true).is_err()).to_be(true)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "host", "clang.exe", false).is_err()).to_be(true)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "host", "cl.exe", false).is_err()).to_be(true)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "host", "gcc.exe", true).is_err()).to_be(true)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "x86_64-pc-windows-msvc", "gcc.exe", false).is_err()).to_be(true)
expect(stage4_windows_c_object_uses_msvc_abi("windows", "host", "compiler-wrapper.exe", true).is_err()).to_be(true)
expect(stage4_windows_c_object_uses_msvc_abi("linux", "host", "clang", true).is_err()).to_be(true)
```

</details>

#### accepts exact ELF Mach-O and COFF dynamic-loader provider contracts

- accepts exact ELF Mach-O and COFF dynamic-loader provider contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts exact ELF Mach-O and COFF dynamic-loader provider contracts")
val elf = "0000000000000000 T spl_dlopen\n0000000000000010 T spl_dlsym\n0000000000000020 T spl_dlclose\n                 U rt_interp_cstr\n                 U dlopen\n                 U dlsym\n                 U dlclose"
val macho = "0000000000000000 T _spl_dlopen\n0000000000000010 T _spl_dlsym\n0000000000000020 T _spl_dlclose\n                 U _rt_interp_cstr\n                 U _dlopen\n                 U _dlsym\n                 U _dlclose"
val msvc = "00000000 T spl_dlopen\n00000010 T spl_dlsym\n00000020 T spl_dlclose\n00000000 A @feat.00\n         U rt_interp_cstr\n         U __imp_LoadLibraryA\n         U __imp_GetProcAddress\n         U __imp_FreeLibrary"
val mingw = "00000000 T _spl_dlopen\n00000010 T _spl_dlsym\n00000020 T _spl_dlclose\n         U _rt_interp_cstr\n         U __imp__LoadLibraryA@4\n         U __imp__GetProcAddress@8\n         U __imp__FreeLibrary@4"
expect(stage4_validate_dynload_provider_symbol_contract(elf, "elf").is_ok()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(macho, "macho").is_ok()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(msvc, "coff-msvc").is_ok()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(mingw, "coff-mingw").is_ok()).to_be(true)
```

</details>

#### rejects incomplete extra repeated and unknown dynamic-loader provider contracts

- rejects incomplete extra repeated and unknown dynamic-loader provider contracts


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects incomplete extra repeated and unknown dynamic-loader provider contracts")
val exact = "0000000000000000 T spl_dlopen\n0000000000000010 T spl_dlsym\n0000000000000020 T spl_dlclose\n                 U rt_interp_cstr\n                 U dlopen\n                 U dlsym\n                 U dlclose"
val missing = exact.replace("0000000000000020 T spl_dlclose\n", "")
val extra_definition = exact + "\n0000000000000030 T spl_hidden"
val extra_undefined = exact + "\n                 U __stack_chk_fail"
val repeated = exact + "\n0000000000000040 T spl_dlopen"
val repeated_undefined = exact + "\n                 U dlopen"
val weak_undefined = exact + "\n                 w rt_hidden_dependency"
val weak_macho_undefined = macho + "\n                 v _rt_hidden_dependency"
val coff = "00000000 T spl_dlopen\n00000010 T spl_dlsym\n00000020 T spl_dlclose\n00000000 A @feat.00\n         U rt_interp_cstr\n         U __imp_LoadLibraryA\n         U __imp_GetProcAddress\n         U __imp_FreeLibrary"
val false_decoration = coff.replace("__imp_LoadLibraryA", "__imp_LoadLibraryA@evil")
val wrong_arity = coff.replace("__imp_LoadLibraryA", "__imp_LoadLibraryA@8")
val repeated_import_alias = coff + "\n         U LoadLibraryA"
expect(stage4_validate_dynload_provider_symbol_contract(missing, "elf").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(extra_definition, "elf").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(extra_undefined, "elf").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(repeated, "elf").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(repeated_undefined, "elf").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(weak_undefined, "elf").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(weak_macho_undefined, "macho").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(false_decoration, "coff-msvc").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(wrong_arity, "coff-msvc").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(repeated_import_alias, "coff-msvc").is_err()).to_be(true)
expect(stage4_validate_dynload_provider_symbol_contract(exact, "wasm").is_err()).to_be(true)
```

</details>

#### defines target-explicit font archive identities and object formats

- defines target-explicit font archive identities and object formats
   - Expected: stage4_font_provider_archive_file("linux", false).unwrap() equals `libsimple_stage4_font.a`
   - Expected: stage4_font_provider_archive_file("macos", false).unwrap() equals `libsimple_stage4_font.a`
   - Expected: stage4_font_provider_archive_file("freebsd", false).unwrap() equals `libsimple_stage4_font.a`
   - Expected: stage4_font_provider_archive_file("windows", false).unwrap() equals `libsimple_stage4_font.a`
   - Expected: stage4_font_provider_archive_file("windows", true).unwrap() equals `simple_stage4_font.lib`
   - Expected: stage4_font_provider_object_format("linux", false).unwrap() equals `elf`
   - Expected: stage4_font_provider_object_format("freebsd", false).unwrap() equals `elf`
   - Expected: stage4_font_provider_object_format("macos", false).unwrap() equals `macho`
   - Expected: stage4_font_provider_object_format("windows", false).unwrap() equals `coff-mingw`
   - Expected: stage4_font_provider_object_format("windows", true).unwrap() equals `coff-msvc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("defines target-explicit font archive identities and object formats")
expect(stage4_font_provider_archive_file("linux", false).unwrap()).to_equal("libsimple_stage4_font.a")
expect(stage4_font_provider_archive_file("macos", false).unwrap()).to_equal("libsimple_stage4_font.a")
expect(stage4_font_provider_archive_file("freebsd", false).unwrap()).to_equal("libsimple_stage4_font.a")
expect(stage4_font_provider_archive_file("windows", false).unwrap()).to_equal("libsimple_stage4_font.a")
expect(stage4_font_provider_archive_file("windows", true).unwrap()).to_equal("simple_stage4_font.lib")
expect(stage4_font_provider_archive_file("linux", true).is_err()).to_be(true)
expect(stage4_font_provider_archive_file("plan9", false).is_err()).to_be(true)
expect(stage4_font_provider_object_format("linux", false).unwrap()).to_equal("elf")
expect(stage4_font_provider_object_format("freebsd", false).unwrap()).to_equal("elf")
expect(stage4_font_provider_object_format("macos", false).unwrap()).to_equal("macho")
expect(stage4_font_provider_object_format("windows", false).unwrap()).to_equal("coff-mingw")
expect(stage4_font_provider_object_format("windows", true).unwrap()).to_equal("coff-msvc")
```

</details>

#### accepts the exact 18-symbol font ABI across hosted object formats

- accepts the exact 18-symbol font ABI across hosted object formats


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts the exact 18-symbol font ABI across hosted object formats")
val exact = """
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
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

- Canonical SPipe generation for source `ec2b5a1b9c4630a9256b0d9d1af1fe29e5c1981e0a72ea5bcf8eb7c86e1ce038`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec2b5a1b9c4630a9256b0d9d1af1fe29e5c1981e0a72ea5bcf8eb7c86e1ce038`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec2b5a1b9c4630a9256b0d9d1af1fe29e5c1981e0a72ea5bcf8eb7c86e1ce038`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/stage4_final_symbol_closure_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 26 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches provider objects only at a portable leaf token boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names and localizes the runtime-native archive for each hosted object ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stages runtime core before owner resolution and includes fork only on POSIX' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
