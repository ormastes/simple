# Guard: paren-less `.length` on a builtin container (String / Array)

> Purpose: Prove that paren-less .length on builtin containers is eliminated at the 6 confirmed sites.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guard: paren-less `.length` on a builtin container (String / Array)

Purpose: Prove that paren-less .length on builtin containers is eliminated at the 6 confirmed sites.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/paren_less_length_accessor_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that paren-less .length on builtin containers is eliminated at the 6 confirmed sites.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### paren-less .length on builtin containers is eliminated at the 6 confirmed sites

#### dap/hooks.spl uses the call form for the stack-frame array

- dap/hooks.spl uses the call form for the stack-frame array
- Verify: dap/hooks.spl uses the call form for the stack-frame array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dap/hooks.spl uses the call form for the stack-frame array")
step("Verify: dap/hooks.spl uses the call form for the stack-frame array")
# @req: REQ-COMP-PAREN-LESS-LENGTH-ON-BUILTIN-CONTAINERS-001
# RED before the fix: the file contained `self.current_frames.length:`.
assert_true(_has(_HOOKS, "self.current_frames.length()"))
assert_false(_has(_HOOKS, "self.current_frames.length:"))
```

</details>

#### dap/hooks.spl uses the call form for both .split() results

- dap/hooks.spl uses the call form for both .split() results
- Verify: dap/hooks.spl uses the call form for both .split() results


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dap/hooks.spl uses the call form for both .split() results")
step("Verify: dap/hooks.spl uses the call form for both .split() results")
# RED before the fix: `parts.length ==` / `mod_parts.length ==`.
assert_true(_has(_HOOKS, "parts.length() == 2"))
assert_true(_has(_HOOKS, "mod_parts.length() == 2"))
assert_false(_has(_HOOKS, "parts.length == 2"))
assert_false(_has(_HOOKS, "mod_parts.length == 2"))
```

</details>

#### disk_image_bake.spl uses the call form for the [u8] payload

- disk_image_bake.spl uses the call form for the [u8] payload
- Verify: disk_image_bake.spl uses the call form for the [u8] payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("disk_image_bake.spl uses the call form for the [u8] payload")
step("Verify: disk_image_bake.spl uses the call form for the [u8] payload")
# RED before the fix: `data.length == 0`.
assert_true(_has(_BAKE, "data.length() == 0"))
assert_false(_has(_BAKE, "data.length == 0"))
```

</details>

#### sshd.spl uses the call form for both fs_exec_resolve() text results

- sshd.spl uses the call form for both fs_exec_resolve() text results
- Verify: sshd.spl uses the call form for both fs_exec_resolve() text results


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sshd.spl uses the call form for both fs_exec_resolve() text results")
step("Verify: sshd.spl uses the call form for both fs_exec_resolve() text results")
# RED before the fix: `resolved.length == 0u64` at :134 and :179.
assert_true(_has(_SSHD, "resolved.length() == 0u64"))
assert_false(_has(_SSHD, "resolved.length == 0u64"))
```

</details>

### the call form is the correct accessor for each receiver shape

#### returns the element count for a plain array (hooks.spl:327 shape)

- returns the element count for a plain array (hooks.spl:327 shape)
- Verify: returns the element count for a plain array (hooks.spl:327 shape)
   - Expected: frames.length() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the element count for a plain array (hooks.spl:327 shape)")
step("Verify: returns the element count for a plain array (hooks.spl:327 shape)")
val frames: [i64] = [10, 20, 30]
expect(frames.length()).to_equal(3)
```

</details>

#### returns the part count for a .split() result (hooks.spl:443/449 shape)

- returns the part count for a .split() result (hooks.spl:443/449 shape)
- Verify: returns the part count for a .split() result (hooks.spl:443/449 shape)
   - Expected: parts.length() equals `2`
   - Expected: mod_parts.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the part count for a .split() result (hooks.spl:443/449 shape)")
step("Verify: returns the part count for a .split() result (hooks.spl:443/449 shape)")
val parts = "a==b".split("==")
expect(parts.length()).to_equal(2)
val mod_parts = "h%3".split("%")
expect(mod_parts.length()).to_equal(2)
```

</details>

#### returns 0 for an empty [u8] payload (disk_image_bake.spl:42 shape)

- returns 0 for an empty [u8] payload (disk_image_bake.spl:42 shape)
- Verify: returns 0 for an empty [u8] payload (disk_image_bake.spl:42 shape)
   - Expected: data.length() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns 0 for an empty [u8] payload (disk_image_bake.spl:42 shape)")
step("Verify: returns 0 for an empty [u8] payload (disk_image_bake.spl:42 shape)")
val data: [u8] = []
expect(data.length()).to_equal(0)
```

</details>

#### returns the byte count for text and compares against a u64 literal (sshd.spl shape)

- returns the byte count for text and compares against a u64 literal (sshd.spl shape)
- Verify: returns the byte count for text and compares against a u64 literal (sshd.spl shape)
   - Expected: resolved.length() equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the byte count for text and compares against a u64 literal (sshd.spl shape)")
step("Verify: returns the byte count for text and compares against a u64 literal (sshd.spl shape)")
val resolved: text = "/usr/bin/clang"
expect(resolved.length()).to_equal(14)
assert_false(resolved.length() == 0u64)
val missing: text = ""
assert_true(missing.length() == 0u64)
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
- `REQ-COMP-PAREN-LESS-LENGTH-ON-BUILTIN-CONTAINERS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c2edb1b1d226b8c88a7434c3857e18af2c6b98031ecc1a6c466122e98f49fcf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c2edb1b1d226b8c88a7434c3857e18af2c6b98031ecc1a6c466122e98f49fcf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c2edb1b1d226b8c88a7434c3857e18af2c6b98031ecc1a6c466122e98f49fcf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/paren_less_length_accessor_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/paren_less_length_accessor_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/paren_less_length_accessor_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/paren_less_length_accessor_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/paren_less_length_accessor_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/paren_less_length_accessor_guard_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dap/hooks.spl uses the call form for the stack-frame array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/paren_less_length_accessor_guard_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dap/hooks.spl uses the call form for both .split() results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/paren_less_length_accessor_guard_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'disk_image_bake.spl uses the call form for the [u8] payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
