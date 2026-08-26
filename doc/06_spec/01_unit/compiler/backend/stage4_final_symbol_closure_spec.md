# @req REQ-SSPEC-COMPILER

> val prefixed = exact.replace(" T rt_", " T _rt_")

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-SSPEC-COMPILER

val prefixed = exact.replace(" T rt_", " T _rt_")

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

val prefixed = exact.replace(" T rt_", " T _rt_")
        expect(stage4_validate_font_provider_symbol_contract(exact, "elf").is_ok()).to_be(true)
        expect(stage4_validate_font_provider_symbol_contract(prefixed, "macho").is_ok()).to_be(true)
        expect(stage4_validate_font_provider_symbol_contract(exact + "00000000 A @feat.00\n", "coff-msvc").is_ok()).to_be(true)
        expect(stage4_validate_font_provider_symbol_contract(prefixed, "coff-mingw").is_ok()).to_be(true)

    it "rejects font ABI drift duplicate exports and runtime dependencies":
        step("rejects font ABI drift duplicate exports and runtime dependencies")
        val exact = "00000000 T rt_font_load_bytes\n00000010 T rt_font_load\n00000020 T rt_font_free\n00000030 T rt_font_glyph_bitmap\n00000040 T rt_font_glyph_index\n00000050 T rt_font_glyph_bitmap_index\n00000060 T rt_font_bitmap_width\n00000070 T rt_font_bitmap_height\n00000080 T rt_font_bitmap_xoff\n00000090 T rt_font_bitmap_yoff\n000000a0 T rt_font_bitmap_get_pixel\n000000b0 T rt_font_bitmap_free\n000000c0 T rt_font_glyph_advance\n000000d0 T rt_font_glyph_advance_index\n000000e0 T rt_font_line_height\n000000f0 T rt_font_ascent\n00000100 T rt_font_descent\n00000110 T rt_font_line_gap\n"
        expect(stage4_validate_font_provider_symbol_contract(exact.replace("00000110 T rt_font_line_gap\n", ""), "elf").is_err()).to_be(true)
        expect(stage4_validate_font_provider_symbol_contract(exact + "00000120 T stbtt_leaked\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_font_provider_symbol_contract(exact + "00000120 T rt_font_load\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_font_provider_symbol_contract(exact + "         U rt_hidden_dependency\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_font_provider_symbol_contract(exact, "wasm").is_err()).to_be(true)

    it "accepts only the exact hosted memtrack provider ABI":
        step("accepts only the exact hosted memtrack provider ABI")
        val exact = "00000000 B g_memtrack_enabled\n00000010 T spl_memtrack_enable\n00000020 T spl_memtrack_disable\n00000030 T spl_memtrack_is_enabled\n00000040 T spl_memtrack_record\n00000050 T spl_memtrack_unrecord\n00000060 T spl_memtrack_snapshot\n00000070 T spl_memtrack_dump_since\n00000080 T spl_memtrack_live_count\n00000090 T spl_memtrack_live_bytes\n000000a0 T spl_memtrack_reset\n000000b0 T spl_memtrack_count_since\n000000c0 T spl_memtrack_bytes_since\n000000d0 T spl_memtrack_set_listener\n000000e0 T spl_memtrack_clear_listener\n         U calloc\n"
        val prefixed = exact.replace(" B g_", " B _g_").replace(" T spl_", " T _spl_")
        expect(stage4_validate_memtrack_provider_symbol_contract(exact, "elf").is_ok()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(prefixed, "macho").is_ok()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(exact + "00000000 A @feat.00\n", "coff-msvc").is_ok()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(prefixed, "coff-mingw").is_ok()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(exact.replace("000000e0 T spl_memtrack_clear_listener\n", ""), "elf").is_err()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(exact + "000000f0 T spl_memtrack_extra\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(exact + "000000f0 T spl_memtrack_enable\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(exact + "         U rt_hidden_dependency\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(exact + "         w spl_hidden_dependency\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_memtrack_provider_symbol_contract(exact, "wasm").is_err()).to_be(true)

    it "accepts the exact hosted time and progress ABI":
        step("accepts the exact hosted time and progress ABI")
        val exact = "00000000 T rt_progress_get_elapsed_seconds\n00000010 T rt_progress_init\n00000020 T rt_progress_reset\n00000030 T rt_time_now_seconds_f64\n00000040 T rt_timestamp_add_days\n00000050 T rt_timestamp_diff_days\n00000060 T rt_timestamp_from_components\n00000070 T rt_timestamp_get_day\n00000080 T rt_timestamp_get_hour\n00000090 T rt_timestamp_get_microsecond\n000000a0 T rt_timestamp_get_minute\n000000b0 T rt_timestamp_get_month\n000000c0 T rt_timestamp_get_second\n000000d0 T rt_timestamp_get_year\n"
        val prefixed = exact.replace(" T rt_", " T _rt_")
        val elf = exact + "         U clock_gettime\n"
        val macho = prefixed + "         U _clock_gettime\n"
        val msvc = exact + "00000000 A @feat.00\n         U rt_time_now_unix_micros\n         U rt_time_now_nanos\n         U __chkstk\n"
        val mingw = prefixed + "         U _rt_time_now_unix_micros\n         U _rt_time_now_nanos\n         U ___chkstk_ms\n"
        expect(stage4_validate_time_provider_symbol_contract(elf, "elf").is_ok()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(macho, "macho").is_ok()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(msvc, "coff-msvc").is_ok()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(mingw, "coff-mingw").is_ok()).to_be(true)

    it "rejects time ABI and runtime dependency drift":
        step("rejects time ABI and runtime dependency drift")
        val exact = "00000000 T rt_progress_get_elapsed_seconds\n00000010 T rt_progress_init\n00000020 T rt_progress_reset\n00000030 T rt_time_now_seconds_f64\n00000040 T rt_timestamp_add_days\n00000050 T rt_timestamp_diff_days\n00000060 T rt_timestamp_from_components\n00000070 T rt_timestamp_get_day\n00000080 T rt_timestamp_get_hour\n00000090 T rt_timestamp_get_microsecond\n000000a0 T rt_timestamp_get_minute\n000000b0 T rt_timestamp_get_month\n000000c0 T rt_timestamp_get_second\n000000d0 T rt_timestamp_get_year\n"
        val windows = exact + "         U rt_time_now_unix_micros\n         U rt_time_now_nanos\n"
        expect(stage4_validate_time_provider_symbol_contract(exact.replace("000000d0 T rt_timestamp_get_year\n", ""), "elf").is_err()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(exact + "000000e0 T rt_time_extra\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(exact + "000000e0 T rt_progress_init\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(exact + "         U rt_hidden_dependency\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(windows.replace("         U rt_time_now_nanos\n", ""), "coff-msvc").is_err()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(windows + "         U spl_hidden_dependency\n", "coff-msvc").is_err()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(windows + "         U rt_time_now_nanos\n", "coff-msvc").is_err()).to_be(true)
        expect(stage4_validate_time_provider_symbol_contract(exact, "wasm").is_err()).to_be(true)

    it "accepts the exact hosted fork ABI and POSIX memtrack dependencies":
        step("accepts the exact hosted fork ABI and POSIX memtrack dependencies")
        val exact = "00000000 T rt_fork_child_setup\n00000010 T rt_fork_parent_wait\n00000020 T rt_fork_parent_wait_bounded\n00000030 T rt_fork_parent_timed_out\n00000040 T rt_fork_parent_signaled\n00000050 T rt_fork_parent_stdout\n00000060 T rt_fork_parent_stderr\n00000070 T rt_fork_child_exit\n"
        val posix_dependencies = "         U g_memtrack_enabled\n         U spl_memtrack_record\n         U spl_memtrack_unrecord\n"
        val prefixed = exact.replace(" T rt_", " T _rt_")
        val prefixed_dependencies = posix_dependencies.replace(" U g_", " U _g_").replace(" U spl_", " U _spl_")
        expect(stage4_validate_fork_provider_symbol_contract(exact + posix_dependencies + "         U poll\n", "elf").is_ok()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(prefixed + prefixed_dependencies + "         U _poll\n", "macho").is_ok()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact + "00000000 A @feat.00\n         U exit\n", "coff-msvc").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(prefixed + "         U _exit\n", "coff-mingw").is_err()).to_be(true)

    it "rejects fork ABI and platform-specific memtrack dependency drift":
        step("rejects fork ABI and platform-specific memtrack dependency drift")
        val exact = "00000000 T rt_fork_child_setup\n00000010 T rt_fork_parent_wait\n00000020 T rt_fork_parent_wait_bounded\n00000030 T rt_fork_parent_timed_out\n00000040 T rt_fork_parent_signaled\n00000050 T rt_fork_parent_stdout\n00000060 T rt_fork_parent_stderr\n00000070 T rt_fork_child_exit\n"
        val dependencies = "         U g_memtrack_enabled\n         U spl_memtrack_record\n         U spl_memtrack_unrecord\n"
        expect(stage4_validate_fork_provider_symbol_contract(exact.replace("00000020 T rt_fork_parent_wait_bounded\n", "") + dependencies, "elf").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact.replace("00000070 T rt_fork_child_exit\n", "") + dependencies, "elf").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact + "00000080 T rt_fork_extra\n" + dependencies, "elf").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact + dependencies.replace("         U g_memtrack_enabled\n", ""), "elf").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact + dependencies.replace("         U spl_memtrack_record\n", ""), "elf").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact + dependencies.replace("         U spl_memtrack_unrecord\n", ""), "elf").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact + dependencies + "         U spl_hidden_dependency\n", "elf").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact + dependencies, "coff-msvc").is_err()).to_be(true)
        expect(stage4_validate_fork_provider_symbol_contract(exact, "wasm").is_err()).to_be(true)

    it "compiles stages validates and cleans the time provider after memtrack":
        step("compiles stages validates and cleans the time provider after memtrack")
        expect(stage4_time_provider_archive_file("linux", false).unwrap()).to_equal("libsimple_stage4_time.a")
        expect(stage4_time_provider_archive_file("windows", true).unwrap()).to_equal("simple_stage4_time.lib")
        expect(stage4_time_provider_archive_file("linux", true).is_err()).to_be(true)
        expect(stage4_time_provider_object_format("freebsd", false).unwrap()).to_equal("elf")
        expect(stage4_time_provider_object_format("macos", false).unwrap()).to_equal("macho")
        expect(stage4_time_provider_object_format("windows", false).unwrap()).to_equal("coff-mingw")
        val compiler_source = rt_file_read_text("src/compiler/70.backend/backend/runtime_compiler.spl") ?? ""
        expect(compiler_source).to_contain("\"runtime_memtrack\", \"runtime_timestamp\", \"runtime_fork\"")
        expect(compiler_source).to_contain("{{object_prefix}}runtime_timestamp{{ext}}")
        val source = compiler_native_link_source()
        val memtrack_pos = source.last_index_of("llvm_stage4_build_memtrack_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
        val time_pos = source.last_index_of("llvm_stage4_build_time_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
        val projection_pos = source.find("llvm_stage4_project_selected_archives(candidate_labels, candidate_paths, selected_archive_indices, stage4_requested_symbols")
        expect(time_pos).to_be_greater_than(memtrack_pos)
        expect(projection_pos).to_be_greater_than(time_pos)
        expect(source).to_contain("llvm_stage4_build_single_object_provider_archive(runtime_objects, \"runtime_timestamp\"")
        expect(source).to_contain("llvm_stage4_candidate_archive_inventory([\"runtime_timestamp\"], [archive_path])")
        expect(source).to_contain("stage4_validate_time_provider_symbol_contract(scans[0], object_format)")
        expect(source).to_contain("\"Stage4 time provider failed: \" + err")
        expect(source).to_contain("file_delete(time_provider_archive)")

    it "stages validates and cleans the fork provider after its memtrack dependency":
        step("stages validates and cleans the fork provider after its memtrack dependency")
        expect(stage4_fork_provider_archive_file("linux", false).unwrap()).to_equal("libsimple_stage4_fork.a")
        expect(stage4_fork_provider_archive_file("windows", true).is_err()).to_be(true)
        expect(stage4_fork_provider_archive_file("windows", false).is_err()).to_be(true)
        expect(stage4_fork_provider_archive_file("linux", true).is_err()).to_be(true)
        expect(stage4_fork_provider_object_format("freebsd", false).unwrap()).to_equal("elf")
        expect(stage4_fork_provider_object_format("macos", false).unwrap()).to_equal("macho")
        expect(stage4_fork_provider_object_format("windows", false).is_err()).to_be(true)
        expect(stage4_fork_provider_object_format("windows", true).is_err()).to_be(true)
        val source = compiler_native_link_source()
        val memtrack_pos = source.last_index_of("llvm_stage4_build_memtrack_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
        val fork_pos = source.last_index_of("llvm_stage4_build_fork_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
        val projection_pos = source.find("llvm_stage4_project_selected_archives(candidate_labels, candidate_paths, selected_archive_indices, stage4_requested_symbols")
        expect(fork_pos).to_be_greater_than(memtrack_pos)
        expect(projection_pos).to_be_greater_than(fork_pos)
        expect(source).to_contain("llvm_stage4_build_single_object_provider_archive(runtime_objects, \"runtime_fork\"")
        expect(source).to_contain("llvm_stage4_candidate_archive_inventory([\"runtime_fork\"], [archive_path])")
        expect(source).to_contain("stage4_validate_fork_provider_symbol_contract(scans[0], object_format)")
        expect(source).to_contain("\"Stage4 fork provider failed: \" + err")
        expect(source).to_contain("file_delete(fork_provider_archive)")

    it "stages validates and cleans the memtrack provider before projection":
        step("stages validates and cleans the memtrack provider before projection")
        expect(stage4_memtrack_provider_archive_file("linux", false).unwrap()).to_equal("libsimple_stage4_memtrack.a")
        expect(stage4_memtrack_provider_archive_file("windows", true).unwrap()).to_equal("simple_stage4_memtrack.lib")
        expect(stage4_memtrack_provider_object_format("macos", false).unwrap()).to_equal("macho")
        expect(stage4_memtrack_provider_object_format("windows", false).unwrap()).to_equal("coff-mingw")
        val source = compiler_native_link_source()
        val font_pos = source.last_index_of("llvm_stage4_build_font_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
        val memtrack_pos = source.last_index_of("llvm_stage4_build_memtrack_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
        val projection_pos = source.find("llvm_stage4_project_selected_archives(candidate_labels, candidate_paths, selected_archive_indices, stage4_requested_symbols")
        expect(memtrack_pos).to_be_greater_than(font_pos)
        expect(projection_pos).to_be_greater_than(memtrack_pos)
        expect(source).to_contain("llvm_stage4_build_single_object_provider_archive(runtime_objects, \"runtime_memtrack\"")
        expect(source).to_contain("llvm_stage4_candidate_archive_inventory([\"runtime_memtrack\"], [archive_path])")
        expect(source).to_contain("stage4_validate_memtrack_provider_symbol_contract(scans[0], object_format)")
        expect(source).to_contain("file_delete(memtrack_provider_archive)")

    it "builds inventories validates and cleans the font provider before projection":
        step("builds inventories validates and cleans the font provider before projection")
        val source = compiler_native_link_source()
        val build_pos = source.find("llvm_stage4_build_font_provider_archive(runtime_objects, hosted_os, stage4_msvc_objects, stage4_msvc_linker, pid)")
        val projection_pos = source.find("llvm_stage4_project_selected_archives(candidate_labels, candidate_paths, selected_archive_indices, stage4_requested_symbols")
        expect(build_pos).to_be_greater_than(-1)
        expect(projection_pos).to_be_greater_than(build_pos)
        expect(source).to_contain("llvm_stage4_candidate_archive_inventory([\"runtime_font\"], [archive_path])")
        expect(source).to_contain("stage4_validate_font_provider_symbol_contract(scans[0], object_format)")
        expect(source).to_contain("file_delete(font_provider_archive)")
        val font_source = rt_file_read_text("src/runtime/runtime_font.c") ?? ""
        expect(font_source).to_contain("#define STBTT_STATIC\n#define STB_TRUETYPE_IMPLEMENTATION")

    it "cleans bootstrap support on every strict provider failure exit":
        step("cleans bootstrap support on every strict provider failure exit")
        val source = compiler_native_link_source()
        val strict_start = source.find("if stage4_requested:")
        val strict_end = source.find("# Step 3: Combine all objects and link")
        val strict_source = source.substring(strict_start, strict_end)
        expect(strict_source).to_contain("file_delete(bootstrap_support_obj)\n            return Err(\"Stage4 strict profile rejects")
        expect(strict_source).to_contain("file_delete(bootstrap_support_obj)\n                return Err(err)")
        expect(strict_source).to_contain("\"Stage4 dynamic-loader provider failed: \" + err")
        expect(strict_source).to_contain("\"Stage4 font provider failed: \" + err")
        expect(strict_source).to_contain("\"Stage4 memtrack provider failed: \" + err")
        expect(strict_source).to_contain("file_delete(bootstrap_support_obj)\n                return Err(\"Stage4 time provider failed")
        expect(strict_source).to_contain("file_delete(bootstrap_support_obj)\n                return Err(\"Stage4 fork provider failed")

    it "rejects hosted constructor and destructor section families":
        step("rejects hosted constructor and destructor section families")
        val headers = ".preinit_array .init_array.42 .ctors .fini_array .dtors __mod_init_func __mod_term_func .CRT$XIA .CRT$XCU .CRT$XPU .CRT$XTU .CRT$XLB"
        val found = stage4_forbidden_archive_sections(headers)
        val joined = found.join(" ")
        expect(joined).to_contain(".preinit_array")
        expect(joined).to_contain(".init_array")
        expect(joined).to_contain(".ctors")
        expect(joined).to_contain(".fini_array")
        expect(joined).to_contain(".dtors")
        expect(joined).to_contain("__mod_init_func")
        expect(joined).to_contain("__mod_term_func")
        expect(joined).to_contain(".CRT$XI")
        expect(joined).to_contain(".CRT$XC")
        expect(joined).to_contain(".CRT$XP")
        expect(joined).to_contain(".CRT$XT")
        expect(joined).to_contain(".CRT$XL")
        expect(stage4_forbidden_archive_sections(".text .data .bss").len()).to_equal(0)

    it "subtracts sibling definitions and returns sorted unique runtime requests":
        step("subtracts sibling definitions and returns sorted unique runtime requests")
        val rows = """
first.o:
                 U rt_cross
                 U rt_need
                 U rt_need
                 U user_helper
                 U rt_unique
                 U rt_weak_lower_fn
                 w rt_weak_lower_fn
                 U rt_weak_lower_data
                 v rt_weak_lower_data
                 U rt_weak_upper_fn
                 W rt_weak_upper_fn
                 U rt_weak_upper_data
                 V rt_weak_upper_data
                 U rt_weak_defined
                 U rt_malformed
second.o:
0000000000000000 T rt_cross
0000000000000000 u rt_unique
0000000000000000 W rt_weak_defined
                 U spl_init_args
                 u rt_malformed
not-an-address W rt_malformed

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
expect(source.contains(".sort()")).to_be(false)
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

- Canonical SPipe generation for source `b913b1991bb417306d1a2fb040c8fb11acf9dd70cc65a13309e7c15a0b20fe55`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b913b1991bb417306d1a2fb040c8fb11acf9dd70cc65a13309e7c15a0b20fe55`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b913b1991bb417306d1a2fb040c8fb11acf9dd70cc65a13309e7c15a0b20fe55`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/stage4_final_symbol_closure_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/backend/stage4_final_symbol_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/stage4_final_symbol_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 26 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches provider objects only at a portable leaf token boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names and localizes the runtime-native archive for each hosted object ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stages runtime core before owner resolution and includes fork only on POSIX' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
