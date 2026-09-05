# if_chain_arm_value_spec

> Purpose: Prove that same-indent leading operator does not continue the previous statement.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# if_chain_arm_value_spec

Purpose: Prove that same-indent leading operator does not continue the previous statement.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/if_chain_arm_value_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that same-indent leading operator does not continue the previous statement.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### same-indent leading operator does not continue the previous statement

#### does not fuse `15` and `-1` into `15 - 1`

- does not fuse `15` and `-1` into `15 - 1`
- Verify: does not fuse `15` and `-1` into `15 - 1`
   - Expected: pure_form() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fuse `15` and `-1` into `15 - 1`")
step("Verify: does not fuse `15` and `-1` into `15 - 1`")
# @req: REQ-COMP-SAME-INDENT-LEADING-OPERATOR-DOES-NOT-CO-001
expect(pure_form()).to_equal(-1)
```

</details>

#### decodes the last hex nibble as 15, not 14

- decodes the last hex nibble as 15, not 14
- Verify: decodes the last hex nibble as 15, not 14
   - Expected: hex_digit("f") equals `15`
   - Expected: hex_digit("F") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decodes the last hex nibble as 15, not 14")
step("Verify: decodes the last hex nibble as 15, not 14")
expect(hex_digit("f")).to_equal(15)
expect(hex_digit("F")).to_equal(15)
```

</details>

#### decodes non-final hex nibbles correctly (unaffected arms)

- decodes non-final hex nibbles correctly (unaffected arms)
- Verify: decodes non-final hex nibbles correctly (unaffected arms)
   - Expected: hex_digit("0") equals `0`
   - Expected: hex_digit("9") equals `9`
   - Expected: hex_digit("a") equals `10`
   - Expected: hex_digit("e") equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decodes non-final hex nibbles correctly (unaffected arms)")
step("Verify: decodes non-final hex nibbles correctly (unaffected arms)")
expect(hex_digit("0")).to_equal(0)
expect(hex_digit("9")).to_equal(9)
expect(hex_digit("a")).to_equal(10)
expect(hex_digit("e")).to_equal(14)
```

</details>

#### returns the -1 sentinel for a non-hex character

- returns the -1 sentinel for a non-hex character
- Verify: returns the -1 sentinel for a non-hex character
   - Expected: hex_digit("z") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the -1 sentinel for a non-hex character")
step("Verify: returns the -1 sentinel for a non-hex character")
expect(hex_digit("z")).to_equal(-1)
```

</details>

#### reproduces with a single arm — chain length is irrelevant

- reproduces with a single arm — chain length is irrelevant
- Verify: reproduces with a single arm — chain length is irrelevant
   - Expected: one_arm("f") equals `15`
   - Expected: one_arm("z") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reproduces with a single arm — chain length is irrelevant")
step("Verify: reproduces with a single arm — chain length is irrelevant")
expect(one_arm("f")).to_equal(15)
expect(one_arm("z")).to_equal(-1)
```

</details>

#### is not stopped by an intervening blank line

- is not stopped by an intervening blank line
- Verify: is not stopped by an intervening blank line
   - Expected: blank_between("f") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is not stopped by an intervening blank line")
step("Verify: is not stopped by an intervening blank line")
expect(blank_between("f")).to_equal(15)
```

</details>

#### does not corrupt an assignment-style arm

- does not corrupt an assignment-style arm
- Verify: does not corrupt an assignment-style arm
   - Expected: assign_variant("f") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not corrupt an assignment-style arm")
step("Verify: does not corrupt an assignment-style arm")
expect(assign_variant("f")).to_equal(15)
```

</details>

### control shapes that must keep working

#### explicit `return -1` tail is unaffected

- explicit `return -1` tail is unaffected
- Verify: explicit `return -1` tail is unaffected
   - Expected: ctl_explicit_return("f") equals `15`
   - Expected: ctl_explicit_return("z") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("explicit `return -1` tail is unaffected")
step("Verify: explicit `return -1` tail is unaffected")
expect(ctl_explicit_return("f")).to_equal(15)
expect(ctl_explicit_return("z")).to_equal(-1)
```

</details>

#### block-form if dedents and is unaffected

- block-form if dedents and is unaffected
- Verify: block-form if dedents and is unaffected
   - Expected: ctl_block_form("f") equals `15`
   - Expected: ctl_block_form("z") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("block-form if dedents and is unaffected")
step("Verify: block-form if dedents and is unaffected")
expect(ctl_block_form("f")).to_equal(15)
expect(ctl_block_form("z")).to_equal(-1)
```

</details>

#### parenthesising the sentinel is a valid workaround

- parenthesising the sentinel is a valid workaround
- Verify: parenthesising the sentinel is a valid workaround
   - Expected: ctl_parenthesised("f") equals `15`
   - Expected: ctl_parenthesised("z") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parenthesising the sentinel is a valid workaround")
step("Verify: parenthesising the sentinel is a valid workaround")
expect(ctl_parenthesised("f")).to_equal(15)
expect(ctl_parenthesised("z")).to_equal(-1)
```

</details>

#### an unsigned tail literal is unaffected

- an unsigned tail literal is unaffected
- Verify: an unsigned tail literal is unaffected
   - Expected: ctl_unsigned_tail("f") equals `15`
   - Expected: ctl_unsigned_tail("z") equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("an unsigned tail literal is unaffected")
step("Verify: an unsigned tail literal is unaffected")
expect(ctl_unsigned_tail("f")).to_equal(15)
expect(ctl_unsigned_tail("z")).to_equal(99)
```

</details>

#### deeper-indented leading operators remain real continuations

- deeper-indented leading operators remain real continuations
- Verify: deeper-indented leading operators remain real continuations
   - Expected: ctl_indented_continuation_plus() equals `15`
   - Expected: ctl_indented_continuation_minus() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("deeper-indented leading operators remain real continuations")
step("Verify: deeper-indented leading operators remain real continuations")
expect(ctl_indented_continuation_plus()).to_equal(15)
expect(ctl_indented_continuation_minus()).to_equal(5)
```

</details>

#### keeps every link of a multi-line continuation chain, not just the first

- keeps every link of a multi-line continuation chain, not just the first
- Verify: keeps every link of a multi-line continuation chain, not just the first
   - Expected: ctl_multiline_chain() equals `abcd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every link of a multi-line continuation chain, not just the first")
step("Verify: keeps every link of a multi-line continuation chain, not just the first")
expect(ctl_multiline_chain()).to_equal("abcd")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-SAME-INDENT-LEADING-OPERATOR-DOES-NOT-CO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a85060831c1ff8e4bb13cac4e5ebd9a2eb2d26a7c466a862d81d35c9a3cb925f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a85060831c1ff8e4bb13cac4e5ebd9a2eb2d26a7c466a862d81d35c9a3cb925f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a85060831c1ff8e4bb13cac4e5ebd9a2eb2d26a7c466a862d81d35c9a3cb925f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/if_chain_arm_value_spec.spl
mirror: doc/06_spec/01_unit/compiler/if_chain_arm_value_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/if_chain_arm_value_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/if_chain_arm_value_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/if_chain_arm_value_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/if_chain_arm_value_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not fuse `15` and `-1` into `15 - 1`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/if_chain_arm_value_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes the last hex nibble as 15, not 14' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/if_chain_arm_value_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes non-final hex nibbles correctly (unaffected arms)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
