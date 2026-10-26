# native_link_hardening_spec

> Purpose: Prove that Native linker hardening.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_link_hardening_spec

Purpose: Prove that Native linker hardening.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/native_link_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Native linker hardening.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Native linker hardening

#### recognizes only strong Vulkan provider definitions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes only strong Vulkan provider definitions
- Verify: recognizes only strong Vulkan provider definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes only strong Vulkan provider definitions")
step("Verify: recognizes only strong Vulkan provider definitions")
# @req: REQ-COMPILER-LINKER-001
expect(llvm_nm_output_has_strong_definition(
    "weak.o:\n                 w rt_vulkan_provider_is_available\nstrong.o:\n0000000000000000 T rt_vulkan_provider_is_available\n",
    "rt_vulkan_provider_is_available"
)).to_be(true)
expect(llvm_nm_output_has_strong_definition(
    "                 W rt_vulkan_provider_is_available\n",
    "rt_vulkan_provider_is_available"
)).to_be(false)
expect(llvm_nm_output_has_strong_definition(
    "                 U rt_vulkan_provider_is_available\n",
    "rt_vulkan_provider_is_available"
)).to_be(false)
expect(llvm_nm_output_has_strong_definition(
    "0000000000000000 T _rt_vulkan_provider_is_available\n",
    "rt_vulkan_provider_is_available"
)).to_be(true)
```

</details>

#### renders archive roots for each native linker family

- renders archive roots for each native linker family
- Verify: renders archive roots for each native linker family
   - Expected: native_retained_symbol_direct_args(roots, "linux") equals `[`
   - Expected: native_retained_symbol_direct_args(roots, "macos") equals `[`
   - Expected: native_retained_symbol_cc_args(roots, "linux") equals `[`
   - Expected: native_retained_symbol_cc_args(roots, "darwin") equals `[`
   - Expected: native_retained_symbol_cc_args(roots, "windows-mingw") equals `[`
   - Expected: native_retained_symbol_msvc_args(roots) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders archive roots for each native linker family")
step("Verify: renders archive roots for each native linker family")
val roots = ["rt_vulkan_provider_is_available"]
expect(native_retained_symbol_direct_args(roots, "linux")).to_equal([
    "--undefined=rt_vulkan_provider_is_available",
    "--export-dynamic-symbol=rt_vulkan_provider_is_available"
])
expect(native_retained_symbol_direct_args(roots, "macos")).to_equal([
    "-u", "_rt_vulkan_provider_is_available",
    "-export_dynamic"
])
expect(native_retained_symbol_cc_args(roots, "linux")).to_equal([
    "-Wl,--undefined=rt_vulkan_provider_is_available",
    "-Wl,--export-dynamic-symbol=rt_vulkan_provider_is_available"
])
expect(native_retained_symbol_cc_args(roots, "darwin")).to_equal([
    "-Wl,-u,_rt_vulkan_provider_is_available",
    "-Wl,-export_dynamic"
])
expect(native_retained_symbol_cc_args(roots, "windows-mingw")).to_equal([
    "-Wl,-u,rt_vulkan_provider_is_available"
])
expect(native_retained_symbol_msvc_args(roots)).to_equal([
    "/INCLUDE:rt_vulkan_provider_is_available",
    "/EXPORT:rt_vulkan_provider_is_available"
])
```

</details>

#### preserves every object in cc fallback arguments

- preserves every object in cc fallback arguments
- Verify: preserves every object in cc fallback arguments
   - Expected: cc_fallback_object_args(["user.o", "runtime.o", "entry.o"]) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves every object in cc fallback arguments")
step("Verify: preserves every object in cc fallback arguments")
expect(cc_fallback_object_args(["user.o", "runtime.o", "entry.o"])).to_equal([
    "user.o", "runtime.o", "entry.o"
])
```

</details>

#### allows duplicate symbols without ignoring unresolved ELF symbols

- allows duplicate symbols without ignoring unresolved ELF symbols
- Verify: allows duplicate symbols without ignoring unresolved ELF symbols
   - Expected: unresolved_symbol_flags_for_unix_linker("linux") equals `[`
   - Expected: unresolved_symbol_flags_for_unix_linker("freebsd") equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows duplicate symbols without ignoring unresolved ELF symbols")
step("Verify: allows duplicate symbols without ignoring unresolved ELF symbols")
expect(unresolved_symbol_flags_for_unix_linker("linux")).to_equal([
    "--allow-multiple-definition"
])
expect(unresolved_symbol_flags_for_unix_linker("freebsd")).to_equal([
    "--allow-multiple-definition"
])
```

</details>

#### skips ELF unresolved-symbol flags on non-ELF direct linkers

- skips ELF unresolved-symbol flags on non-ELF direct linkers
- Verify: skips ELF unresolved-symbol flags on non-ELF direct linkers
   - Expected: unresolved_symbol_flags_for_unix_linker("macos") equals `[]`
   - Expected: unresolved_symbol_flags_for_unix_linker("darwin") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips ELF unresolved-symbol flags on non-ELF direct linkers")
step("Verify: skips ELF unresolved-symbol flags on non-ELF direct linkers")
expect(unresolved_symbol_flags_for_unix_linker("macos")).to_equal([])
expect(unresolved_symbol_flags_for_unix_linker("darwin")).to_equal([])
```

</details>

#### allows duplicate symbols without ignoring unresolved cc symbols

- allows duplicate symbols without ignoring unresolved cc symbols
- Verify: allows duplicate symbols without ignoring unresolved cc symbols
   - Expected: unresolved_symbol_flags_for_cc("Linux") equals `[`
   - Expected: unresolved_symbol_flags_for_cc("FreeBSD") equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows duplicate symbols without ignoring unresolved cc symbols")
step("Verify: allows duplicate symbols without ignoring unresolved cc symbols")
expect(unresolved_symbol_flags_for_cc("Linux")).to_equal([
    "-Wl,--allow-multiple-definition"
])
expect(unresolved_symbol_flags_for_cc("FreeBSD")).to_equal([
    "-Wl,--allow-multiple-definition"
])
```

</details>

#### keeps unresolved Windows symbols fatal

- keeps unresolved Windows symbols fatal
- Verify: keeps unresolved Windows symbols fatal
   - Expected: msvc_duplicate_symbol_flag() equals `/FORCE:MULTIPLE`
   - Expected: msvc_duplicate_symbol_flag() does not contain `UNRESOLVED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps unresolved Windows symbols fatal")
step("Verify: keeps unresolved Windows symbols fatal")
expect(msvc_duplicate_symbol_flag()).to_equal("/FORCE:MULTIPLE")
expect(msvc_duplicate_symbol_flag().contains("UNRESOLVED")).to_equal(false)
```

</details>

#### lets strict links disable duplicate forgiveness and cc fallback

- lets strict links disable duplicate forgiveness and cc fallback
- Verify: lets strict links disable duplicate forgiveness and cc fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lets strict links disable duplicate forgiveness and cc fallback")
step("Verify: lets strict links disable duplicate forgiveness and cc fallback")
val native = rt_file_read_text("src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl") ?? ""
val llvm = compiler_native_link_source()
expect(native).to_contain("if config.allow_duplicate_definitions:")
expect(native).to_contain("if not config.allow_cc_fallback:")
expect(llvm).to_contain("allow_duplicate_definitions: not stage4_requested")
expect(llvm).to_contain("allow_cc_fallback: not stage4_requested")
```

</details>

#### makes strict SimpleOS links disable fabrication debt baselines

- makes strict SimpleOS links disable fabrication debt baselines
- Verify: makes strict SimpleOS links disable fabrication debt baselines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("makes strict SimpleOS links disable fabrication debt baselines")
step("Verify: makes strict SimpleOS links disable fabrication debt baselines")
val llvm = compiler_native_link_source()
expect(llvm).to_contain("env_get(\"SIMPLE_NO_STUB_FALLBACK\")")
expect(llvm).to_contain("if flight_closure: {} else: simpleos_simple_symbol_baseline(entry_key)")
expect(llvm).to_contain("if flight_closure: {} else: simpleos_fabricated_baseline(entry_key)")
```

</details>

#### WP-10: a flight-closure link (critical profile OR strict env) disables the fabrication baseline exactly like strict_no_stub_fallback

- WP-10: a flight-closure link (critical profile OR strict env) disables the fabrication baseline exactly like strict_no_stub_fallback
- Verify: WP-10: a flight-closure link (critical profile OR strict env) disables the fabrication baseline exactly like strict_no_stub_fallback
   - Expected: llvm contains `val baseline = if flight_closure: {} else: simpleos_fabricated_baseline(entry... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("WP-10: a flight-closure link (critical profile OR strict env) disables the fabrication baseline exactly like strict_no_stub_fallback")
step("Verify: WP-10: a flight-closure link (critical profile OR strict env) disables the fabrication baseline exactly like strict_no_stub_fallback")
"""
doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md
WP-10: `simpleos_check_no_fabricated_rt_stubs`'s baseline exemption
used to be gated ONLY by SIMPLE_NO_STUB_FALLBACK=1 -- a `critical`
assurance-profile link got the same lenient baseline exemption as
every other profile, so a previously-baselined fabricated weak
NIL-returning stub (auto_stubs.c) could still ship silently. This
pins that `flight_closure` now ORs in the critical profile, routed
through the WP-3 canonical policy resolver rather than a hardcoded
string compare.
"""
val llvm = compiler_native_link_source()
expect(llvm).to_contain("use compiler.common.assurance.policy." + "{" + "strictness_for_profile_name" + "}")
expect(llvm).to_contain("use compiler.common.assurance.policy_schema." + "{" + "AssuranceStrictness" + "}")
expect(llvm).to_contain("val flight_closure_profile = env_get(\"SIMPLE_SAFETY_PROFILE\") ?? \"\"")
expect(llvm).to_contain("val flight_closure = strict_no_stub_fallback or strictness_for_profile_name(flight_closure_profile).at_least(AssuranceStrictness.Critical)")
# non-flight-closure (moderate/strict/robust, SIMPLE_NO_STUB_FALLBACK
# unset) must keep today's fabrication-tolerant behaviour: the
# baseline lookup is still reachable, not unconditionally emptied.
expect(llvm.contains("val baseline = if flight_closure: {} else: simpleos_fabricated_baseline(entry_key)")).to_equal(true)
```

</details>

#### requires complete CRT endpoints before direct linking

- requires complete CRT endpoints before direct linking
- Verify: requires complete CRT endpoints before direct linking
   - Expected: crt does not contain `found: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("requires complete CRT endpoints before direct linking")
step("Verify: requires complete CRT endpoints before direct linking")
val crt = rt_file_read_text("src/compiler/70.backend/linker/crt_discovery.spl") ?? ""
expect(crt).to_contain("found: found_crtbegin != \"\" and found_crtend != \"\"")
expect(crt.contains("found: true")).to_equal(false)
```

</details>

#### uses configured and architecture-default Homebrew prefixes

- uses configured and architecture-default Homebrew prefixes
- Verify: uses configured and architecture-default Homebrew prefixes
   - Expected: macos_homebrew_prefix("/custom/brew", "x86_64") equals `/custom/brew`
   - Expected: macos_homebrew_prefix("", "x86_64") equals `/usr/local`
   - Expected: macos_homebrew_prefix("", "aarch64") equals `/opt/homebrew`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses configured and architecture-default Homebrew prefixes")
step("Verify: uses configured and architecture-default Homebrew prefixes")
expect(macos_homebrew_prefix("/custom/brew", "x86_64")).to_equal("/custom/brew")
expect(macos_homebrew_prefix("", "x86_64")).to_equal("/usr/local")
expect(macos_homebrew_prefix("", "aarch64")).to_equal("/opt/homebrew")
```

</details>

#### skips cc fallback unresolved-symbol flags on Darwin

- skips cc fallback unresolved-symbol flags on Darwin
- Verify: skips cc fallback unresolved-symbol flags on Darwin
   - Expected: unresolved_symbol_flags_for_cc("Darwin") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips cc fallback unresolved-symbol flags on Darwin")
step("Verify: skips cc fallback unresolved-symbol flags on Darwin")
expect(unresolved_symbol_flags_for_cc("Darwin")).to_equal([])
```

</details>

#### recognizes only canonical native-all archive leaves

- recognizes only canonical native-all archive leaves
- Verify: recognizes only canonical native-all archive leaves


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes only canonical native-all archive leaves")
step("Verify: recognizes only canonical native-all archive leaves")
expect(native_all_input_present(["/tmp/libsimple_native_all.a"])).to_be(true)
expect(native_all_input_present(["C:\\runtime\\SIMPLE_NATIVE_ALL.LIB"])).to_be(true)
expect(native_all_input_present(["/tmp/libsimple_runtime.a"])).to_be(false)
expect(native_all_input_present(["/tmp/libsimple_native_all.dll.a"])).to_be(false)
expect(native_all_input_present(["/tmp/libsimple_native_all.a.tmp"])).to_be(false)
expect(native_all_input_present(["/tmp/my_libsimple_native_all.a"])).to_be(false)
```

</details>

#### keeps native-all support out of core-only links

- keeps native-all support out of core-only links
- Verify: keeps native-all support out of core-only links
   - Expected: native_all_gnu_support_args(["runtime.o"], os, "/brew") equals `[]`
   - Expected: native_all_msvc_support_libraries(["runtime.obj"]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps native-all support out of core-only links")
step("Verify: keeps native-all support out of core-only links")
for os in ["linux", "macos", "freebsd", "windows-mingw"]:
    expect(native_all_gnu_support_args(["runtime.o"], os, "/brew")).to_equal([])
expect(native_all_msvc_support_libraries(["runtime.obj"])).to_equal([])
```

</details>

#### supplies hosted native-all transitive dependencies

- supplies hosted native-all transitive dependencies
- Verify: supplies hosted native-all transitive dependencies
   - Expected: native_all_gnu_support_args(archive, "linux", "") equals `[`
   - Expected: macos[0] equals `-u`
   - Expected: macos[1] equals `_rt_vulkan_provider_is_available`
   - Expected: native_all_gnu_support_args(archive, "freebsd", "") equals `[`
   - Expected: mingw[0] equals `-u`
   - Expected: mingw[1] equals `rt_vulkan_provider_is_available`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supplies hosted native-all transitive dependencies")
step("Verify: supplies hosted native-all transitive dependencies")
val archive = ["/runtime/libsimple_native_all.a"]
expect(native_all_gnu_support_args(archive, "linux", "")).to_equal([
    "-u", "rt_vulkan_provider_is_available", "-lstdc++", "-lunwind", "-lsqlite3", "-lz", "-lzstd", "-ltinfo", "-lffi", "-lxml2", "-lncurses"
])
val macos = native_all_gnu_support_args(archive, "macos", "/custom/brew")
expect(macos[0]).to_equal("-u")
expect(macos[1]).to_equal("_rt_vulkan_provider_is_available")
expect(macos).to_contain("-L/custom/brew/lib")
expect(macos).to_contain("CoreFoundation")
expect(macos).to_contain("AppKit")
expect(macos).to_contain("CoreGraphics")
expect(native_all_gnu_support_args(archive, "freebsd", "")).to_equal([
    "-u", "rt_vulkan_provider_is_available", "-L/usr/local/lib", "-lc++", "-lexecinfo", "-lz", "-lzstd", "-lutil", "-lrt"
])
val mingw = native_all_gnu_support_args(["C:\\runtime\\libsimple_native_all.a"], "windows-mingw", "")
expect(mingw[0]).to_equal("-u")
expect(mingw[1]).to_equal("rt_vulkan_provider_is_available")
expect(mingw).to_contain("-ldbghelp")
expect(mingw).to_contain("-lruntimeobject")
expect(mingw).to_contain("-luser32")
expect(mingw).to_contain("-lgdi32")
expect(mingw).to_contain("-lgcc")
val msvc = native_all_msvc_support_libraries(["C:\\runtime\\simple_native_all.lib"])
expect(msvc).to_contain("dbghelp.lib")
expect(msvc).to_contain("gdi32.lib")
expect(msvc).to_contain("vcruntime.lib")
```

</details>

#### wires the shared policy into every native and shared linker path

- wires the shared policy into every native and shared linker path
- Verify: wires the shared policy into every native and shared linker path
   - Expected: native.split("native_all_gnu_support_args").len() - 1 equals `4`
   - Expected: shared.split("native_all_gnu_support_args").len() - 1 equals `3`
   - Expected: native.split("native_all_msvc_support_libraries").len() - 1 equals `1`
   - Expected: shared.split("native_all_msvc_support_libraries").len() - 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wires the shared policy into every native and shared linker path")
step("Verify: wires the shared policy into every native and shared linker path")
val native = rt_file_read_text("src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl")
val shared = rt_file_read_text("src/compiler/70.backend/linker/_LinkerWrapper/shared_linking.spl")
expect(native.split("native_all_gnu_support_args").len() - 1).to_equal(4)
expect(shared.split("native_all_gnu_support_args").len() - 1).to_equal(3)
expect(native.split("native_all_msvc_support_libraries").len() - 1).to_equal(1)
expect(shared.split("native_all_msvc_support_libraries").len() - 1).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-LINKER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fafd1e278fc82472b36ac844a8d30e982dc5afe6f79093e340b814d547c83fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fafd1e278fc82472b36ac844a8d30e982dc5afe6f79093e340b814d547c83fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fafd1e278fc82472b36ac844a8d30e982dc5afe6f79093e340b814d547c83fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/linker/native_link_hardening_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/native_link_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/native_link_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/native_link_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/native_link_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/native_link_hardening_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes only strong Vulkan provider definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/native_link_hardening_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders archive roots for each native linker family' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/native_link_hardening_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves every object in cc fallback arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
