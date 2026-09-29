# safety_checker_unsafe_boundary_spec

> Purpose: Prove that safety checker unsafe boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# safety_checker_unsafe_boundary_spec

Purpose: Prove that safety checker unsafe boundary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that safety checker unsafe boundary.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### safety checker unsafe boundary

#### warns on raw-pointer primitive call outside unsafe

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- warns on raw-pointer primitive call outside unsafe
- Verify: warns on raw-pointer primitive call outside unsafe
   - Expected: count_kind(errors, "raw_ptr") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on raw-pointer primitive call outside unsafe")
step("Verify: warns on raw-pointer primitive call outside unsafe")
# @req: REQ-COMPILER-SEMANTICS-001
val src = "extern fn rt_alloc(size: i64) -> i64\n" +
    "fn use_raw() -> i64:\n" +
    "    val p = rt_alloc(16)\n" +
    "    p\n"
val errors = check_source(src, "safety_raw_outside")
expect(count_kind(errors, "raw_ptr")).to_equal(1)
```

</details>

#### is silent for the same raw-pointer call inside unsafe

- is silent for the same raw-pointer call inside unsafe
- Verify: is silent for the same raw-pointer call inside unsafe
   - Expected: count_kind(errors, "raw_ptr") equals `0`
   - Expected: count_kind(errors, "ffi") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is silent for the same raw-pointer call inside unsafe")
step("Verify: is silent for the same raw-pointer call inside unsafe")
val src = "extern fn rt_alloc(size: i64) -> i64\n" +
    "fn use_raw() -> i64:\n" +
    "    unsafe:\n" +
    "        val p = rt_alloc(16)\n" +
    "    0\n"
val errors = check_source(src, "safety_raw_inside")
expect(count_kind(errors, "raw_ptr")).to_equal(0)
expect(count_kind(errors, "ffi")).to_equal(0)
```

</details>

#### still warns on inline asm outside unsafe

- still warns on inline asm outside unsafe
- Verify: still warns on inline asm outside unsafe
   - Expected: count_kind(errors, "asm") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still warns on inline asm outside unsafe")
step("Verify: still warns on inline asm outside unsafe")
# Raw (single-quoted) segment for the `{ nop }` text: a double-quoted
# literal auto-interpolates `{...}`, and the self-hosted frontend
# eagerly lowers/evaluates that embedded `nop` as a real identifier
# expression -- unrelated to inline-asm lowering itself (same failure
# mode reproduces on the pre-existing, unrelated
# inline_asm_core_parser_spec.spl, which is red for the same reason).
val src = "fn touch():\n" +
    '    asm { nop }' + "\n"
val errors = check_source(src, "safety_asm_outside")
expect(count_kind(errors, "asm")).to_equal(1)
```

</details>

#### is silent for inline asm inside unsafe

- is silent for inline asm inside unsafe
- Verify: is silent for inline asm inside unsafe
   - Expected: count_kind(errors, "asm") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is silent for inline asm inside unsafe")
step("Verify: is silent for inline asm inside unsafe")
val src = "fn touch():\n" +
    "    unsafe:\n" +
    '        asm { nop }' + "\n"
val errors = check_source(src, "safety_asm_inside")
expect(count_kind(errors, "asm")).to_equal(0)
```

</details>

#### warns on module extern fn (FFI) call outside unsafe

- warns on module extern fn (FFI) call outside unsafe
- Verify: warns on module extern fn (FFI) call outside unsafe
   - Expected: count_kind(errors, "ffi") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on module extern fn (FFI) call outside unsafe")
step("Verify: warns on module extern fn (FFI) call outside unsafe")
val src = "extern fn my_device_poke(x: i64) -> i64\n" +
    "fn use_ffi() -> i64:\n" +
    "    my_device_poke(1)\n"
val errors = check_source(src, "safety_ffi_outside")
expect(count_kind(errors, "ffi")).to_equal(1)
```

</details>

#### warns on imported-style raw runtime call outside unsafe

- warns on imported-style raw runtime call outside unsafe
- Verify: imported rt identity remains ffi-unsafe
   - Expected: count_kind(errors, "ffi") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on imported-style raw runtime call outside unsafe")
step("Verify: imported rt identity remains ffi-unsafe")
val src = "fn rt_imported_probe() -> i64:\n" +
    "    1\n" +
    "fn use_imported_raw() -> i64:\n" +
    "    rt_imported_probe()\n"
val errors = check_source(src, "safety_imported_ffi_outside")
expect(count_kind(errors, "ffi")).to_equal(1)
```

</details>

#### accepts imported-style raw runtime call inside unsafe

- accepts imported-style raw runtime call inside unsafe
- Verify: minimal ffi boundary admits imported rt identity
   - Expected: count_kind(errors, "ffi") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts imported-style raw runtime call inside unsafe")
step("Verify: minimal ffi boundary admits imported rt identity")
val src = "fn rt_imported_probe() -> i64:\n" +
    "    1\n" +
    "fn use_imported_raw() -> i64:\n" +
    "    unsafe(capabilities: [ffi]):\n" +
    "        rt_imported_probe()\n"
val errors = check_source(src, "safety_imported_ffi_inside")
expect(count_kind(errors, "ffi")).to_equal(0)
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
- `REQ-COMPILER-SEMANTICS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb4cd627660b2df6ace06f9cbb67344871a7804ff7c8477c47c3445d643be6c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb4cd627660b2df6ace06f9cbb67344871a7804ff7c8477c47c3445d643be6c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb4cd627660b2df6ace06f9cbb67344871a7804ff7c8477c47c3445d643be6c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on raw-pointer primitive call outside unsafe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is silent for the same raw-pointer call inside unsafe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/safety_checker_unsafe_boundary_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still warns on inline asm outside unsafe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
