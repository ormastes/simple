# protection_spec

> Word document-protection (Restrict Editing) spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# protection_spec

Word document-protection (Restrict Editing) spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word/protection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Word document-protection (Restrict Editing) spec.

Ground-truth permission matrix (enforced == true unless noted):
- none:            can_edit_body true,  can_add_comment true,  requires_password false, xml ""
- readOnly:        can_edit_body false, can_add_comment false, requires_password (per password)
- comments:        can_edit_body false, can_add_comment true
- forms:           can_edit_body false, can_add_comment false
- trackedChanges:  can_edit_body true (edits allowed, just tracked), can_add_comment true
- any mode with enforced == false: can_edit_body true, can_add_comment true (no restriction)

## Scenarios

### protection_none: no protection at all

#### has mode none, is not enforced, and has no password

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has mode none, is not enforced, and has no password
   - Expected: prot.mode equals `none`
   - Expected: prot.password_hash equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has mode none, is not enforced, and has no password")
val prot = protection_none()
expect(prot.mode).to_equal("none")
assert_false(prot.enforced)
expect(prot.password_hash).to_equal("")
```

</details>

#### allows body edits and comments

- allows body edits and comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows body edits and comments")
val prot = protection_none()
assert_true(can_edit_body(prot))
assert_true(can_add_comment(prot))
```

</details>

#### requires no password

- requires no password


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires no password")
val prot = protection_none()
assert_false(requires_password(prot))
```

</details>

#### renders to the empty XML fragment

- renders to the empty XML fragment
   - Expected: protection_to_xml(prot) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders to the empty XML fragment")
val prot = protection_none()
expect(protection_to_xml(prot)).to_equal("")
```

</details>

### protection_read_only: enforced read-only with a password

#### blocks body edits and comments

- blocks body edits and comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks body edits and comments")
val prot = protection_read_only("abc123")
assert_false(can_edit_body(prot))
assert_false(can_add_comment(prot))
```

</details>

#### requires a password

- requires a password


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a password")
val prot = protection_read_only("abc123")
assert_true(requires_password(prot))
```

</details>

#### renders edit mode, enforcement, and password hash in the XML

- renders edit mode, enforcement, and password hash in the XML


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders edit mode, enforcement, and password hash in the XML")
val prot = protection_read_only("abc123")
val xml = protection_to_xml(prot)
expect(xml).to_contain("w:edit=\"readOnly\"")
expect(xml).to_contain("w:enforcement=\"1\"")
expect(xml).to_contain("w:hash=\"abc123\"")
```

</details>

### comments mode: enforced comment-only protection

#### blocks body edits but allows adding comments

- blocks body edits but allows adding comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks body edits but allows adding comments")
val prot = protection_new("comments", true, "")
assert_false(can_edit_body(prot))
assert_true(can_add_comment(prot))
```

</details>

#### requires no password when password_hash is empty

- requires no password when password_hash is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires no password when password_hash is empty")
val prot = protection_new("comments", true, "")
assert_false(requires_password(prot))
```

</details>

### forms mode: enforced forms-only protection

#### blocks both body edits and comments

- blocks both body edits and comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks both body edits and comments")
val prot = protection_new("forms", true, "")
assert_false(can_edit_body(prot))
assert_false(can_add_comment(prot))
```

</details>

### trackedChanges mode: enforced tracked editing

#### allows body edits (tracked) and allows comments

- allows body edits (tracked) and allows comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows body edits (tracked) and allows comments")
val prot = protection_new("trackedChanges", true, "")
assert_true(can_edit_body(prot))
assert_true(can_add_comment(prot))
```

</details>

### non-enforced protection: enforcement off means no restriction

#### allows body edits and comments even in readOnly mode

- allows body edits and comments even in readOnly mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows body edits and comments even in readOnly mode")
val prot = protection_new("readOnly", false, "")
assert_true(can_edit_body(prot))
assert_true(can_add_comment(prot))
```

</details>

### protection_summary: readable one-line description

#### formats none as just \

- formats none as just \
   - Expected: protection_summary(prot) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats none as just \")
val prot = protection_none()
expect(protection_summary(prot)).to_equal("none")
```

</details>

#### formats enforced readOnly with a password

- formats enforced readOnly with a password
   - Expected: protection_summary(prot) equals `readOnly (enforced, password)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats enforced readOnly with a password")
val prot = protection_read_only("abc123")
expect(protection_summary(prot)).to_equal("readOnly (enforced, password)")
```

</details>

#### formats enforced protection without a password

- formats enforced protection without a password
   - Expected: protection_summary(prot) equals `forms (enforced)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats enforced protection without a password")
val prot = protection_new("forms", true, "")
expect(protection_summary(prot)).to_equal("forms (enforced)")
```

</details>

#### formats non-enforced protection

- formats non-enforced protection
   - Expected: protection_summary(prot) equals `comments (not enforced)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats non-enforced protection")
val prot = protection_new("comments", false, "")
expect(protection_summary(prot)).to_equal("comments (not enforced)")
```

</details>

### deliberate-fail probe (must be fixed to green before landing)

#### confirms trackedChanges still permits body edits when enforced

- confirms trackedChanges still permits body edits when enforced


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("confirms trackedChanges still permits body edits when enforced")
val prot = protection_new("trackedChanges", true, "")
# ground truth: trackedChanges allows edits (they are tracked, not blocked).
assert_true(can_edit_body(prot))
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5a73a18e0850810de5d78451974ab6cae6e344b077afb5076c5a0c1875a953a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a73a18e0850810de5d78451974ab6cae6e344b077afb5076c5a0c1875a953a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a73a18e0850810de5d78451974ab6cae6e344b077afb5076c5a0c1875a953a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/word/protection_spec.spl
mirror: doc/06_spec/01_unit/app/office/word/protection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/word/protection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/word/protection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/word/protection_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has mode none, is not enforced, and has no password' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/word/protection_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows body edits and comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/word/protection_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires no password' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
