# Contract spec: test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl` |
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
`bin/simple test test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl` and a green Results line.

## Scenarios

### Stage4 selected archive projection

#### keeps entry runtime intrinsics and memtrack state in the requested closure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps entry runtime intrinsics and memtrack state in the requested closure
   - Expected: stage4_requested_from_nm_output(elf, false) equals `[`
   - Expected: stage4_requested_from_nm_output(macho, true) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps entry runtime intrinsics and memtrack state in the requested closure")
val elf = "00000000 T __simple_main\n         U __simple_runtime_shutdown\n         U __simple_runtime_init\n         U __simple_pow\n         U g_memtrack_enabled\n"
expect(stage4_requested_from_nm_output(elf, false)).to_equal([
    "__simple_pow", "__simple_runtime_init", "__simple_runtime_shutdown", "g_memtrack_enabled"
])
val macho = elf.replace(" T __simple_main", " T ___simple_main").replace(" U __simple_", " U ___simple_").replace(" U g_memtrack_enabled", " U _g_memtrack_enabled")
expect(stage4_requested_from_nm_output(macho, true)).to_equal([
    "__simple_pow", "__simple_runtime_init", "__simple_runtime_shutdown", "g_memtrack_enabled"
])
```

</details>

#### localizes every transitive and non-runtime definition outside the requested roots

- localizes every transitive and non-runtime definition outside the requested roots
   - Expected: symbols equals `["helper_private", "rt_dependency"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("localizes every transitive and non-runtime definition outside the requested roots")
val nm = "00000000 T rt_root\n00000010 T rt_dependency\n00000020 T helper_private\n         U malloc\n"
val symbols = stage4_projection_localization_symbols(nm, "elf", ["rt_root"]).unwrap()
expect(symbols).to_equal(["helper_private", "rt_dependency"])
```

</details>

#### preserves raw Mach-O names in the localization list

- preserves raw Mach-O names in the localization list
   - Expected: symbols equals `["_helper_private", "_rt_dependency"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves raw Mach-O names in the localization list")
val nm = "00000000 T _spl_root\n00000010 T _rt_dependency\n00000020 T _helper_private\n         U _malloc\n"
val symbols = stage4_projection_localization_symbols(nm, "macho", ["spl_root"]).unwrap()
expect(symbols).to_equal(["_helper_private", "_rt_dependency"])
```

</details>

#### accepts an exact projected global ABI with system dependencies only

- accepts an exact projected global ABI with system dependencies only


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts an exact projected global ABI with system dependencies only")
val nm = "00000000 T rt_root\n00000010 T spl_other_root\n         U malloc\n"
expect(stage4_validate_projection_symbol_contract(nm, "elf", ["rt_root", "spl_other_root"]).is_ok()).to_be(true)
```

</details>

#### rejects missing duplicate repeated and non-runtime roots

- rejects missing duplicate repeated and non-runtime roots


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects missing duplicate repeated and non-runtime roots")
val missing = stage4_projection_localization_symbols("00000000 T rt_other\n", "elf", ["rt_root"])
val duplicate_definition = stage4_projection_localization_symbols("00000000 T rt_root\n00000010 T rt_root\n", "elf", ["rt_root"])
val duplicate_root = stage4_projection_localization_symbols("00000000 T rt_root\n", "elf", ["rt_root", "rt_root"])
val non_runtime = stage4_projection_localization_symbols("00000000 T helper\n", "elf", ["helper"])
expect(missing.is_err()).to_be(true)
expect(duplicate_definition.is_err()).to_be(true)
expect(duplicate_root.is_err()).to_be(true)
expect(non_runtime.is_err()).to_be(true)
```

</details>

#### rejects unresolved runtime dependencies and unsupported object formats

- rejects unresolved runtime dependencies and unsupported object formats


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects unresolved runtime dependencies and unsupported object formats")
val unresolved = stage4_projection_localization_symbols("00000000 T rt_root\n         U spl_missing\n", "elf", ["rt_root"])
val unsupported = stage4_projection_localization_symbols("00000000 T rt_root\n", "coff-msvc", ["rt_root"])
val empty = stage4_projection_localization_symbols("00000000 T rt_root\n", "elf", [])
expect(unresolved.is_err()).to_be(true)
expect(unsupported.is_err()).to_be(true)
expect(empty.is_err()).to_be(true)
```

</details>

#### rejects globals retained after localization

- rejects globals retained after localization


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects globals retained after localization")
val nm = "00000000 T rt_root\n00000010 T rt_extra\n"
expect(stage4_validate_projection_symbol_contract(nm, "elf", ["rt_root"]).is_err()).to_be(true)
```

</details>

#### wires roots through a cycle-safe localized one-member capsule before strict linking

- wires roots through a cycle-safe localized one-member capsule before strict linking


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wires roots through a cycle-safe localized one-member capsule before strict linking")
val source = compiler_native_link_source()
val project_pos = source.find("llvm_stage4_project_selected_archives(candidate_labels, candidate_paths, selected_archive_indices, stage4_requested_symbols")
val step3_pos = source.find("# Step 3: Combine all objects and link")
val link_pos = source.find("val link_result = link_to_native(all_objects, output, link_config)")
expect(project_pos).to_be_greater_than(-1)
expect(step3_pos).to_be_greater_than(project_pos)
expect(link_pos).to_be_greater_than(step3_pos)
expect(source).to_contain("closure_args = closure_args.push(\"-Wl,--start-group\")")
expect(source).to_contain("closure_args = closure_args.push(\"-Wl,--end-group\")")
expect(source).to_contain("closure_args = closure_args.push(\"-Wl,-u,_{{symbol}}\")")
expect(source).to_contain("closure_args = closure_args.push(\"-Wl,-force_load,\" + path)")
expect(source).to_contain("stage4_projection_localization_symbols(closure_nm_out, object_format, requested_symbols)")
expect(source).to_contain("stage4_validate_projection_symbol_contract(scans[0], object_format, requested_symbols)")
expect(source).to_contain("members_out.replace(\"\\r\", \"\").trim() != \"stage4_selected_local.o\"")
expect(source).to_contain("all_objects = all_objects.push(entry_obj_path)\n        all_objects = all_objects.push(stage4_projection_capsule)")
expect(source).to_contain("allow_duplicate_definitions: not stage4_requested")
expect(source).to_contain("allow_cc_fallback: not stage4_requested")
expect(source).to_not_contain("Stage4 strict archive projection is unavailable")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `83142895ec9f73d10ea56d74f74d3aed97e6c12a92a9a0ac4008e5ebfb0806f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83142895ec9f73d10ea56d74f74d3aed97e6c12a92a9a0ac4008e5ebfb0806f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83142895ec9f73d10ea56d74f74d3aed97e6c12a92a9a0ac4008e5ebfb0806f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/stage4_selected_archive_projection_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps entry runtime intrinsics and memtrack state in the requested closure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'localizes every transitive and non-runtime definition outside the requested roots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/stage4_selected_archive_projection_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves raw Mach-O names in the localization list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
