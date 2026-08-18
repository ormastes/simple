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
| Updated | 2026-08-18 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_none()
expect(prot.mode).to_equal("none")
assert_false(prot.enforced)
expect(prot.password_hash).to_equal("")
```

</details>

#### allows body edits and comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_none()
assert_true(can_edit_body(prot))
assert_true(can_add_comment(prot))
```

</details>

#### requires no password

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_none()
assert_false(requires_password(prot))
```

</details>

#### renders to the empty XML fragment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_none()
expect(protection_to_xml(prot)).to_equal("")
```

</details>

### protection_read_only: enforced read-only with a password

#### blocks body edits and comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_read_only("abc123")
assert_false(can_edit_body(prot))
assert_false(can_add_comment(prot))
```

</details>

#### requires a password

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_read_only("abc123")
assert_true(requires_password(prot))
```

</details>

#### renders edit mode, enforcement, and password hash in the XML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_read_only("abc123")
val xml = protection_to_xml(prot)
expect(xml).to_contain("w:edit=\"readOnly\"")
expect(xml).to_contain("w:enforcement=\"1\"")
expect(xml).to_contain("w:hash=\"abc123\"")
```

</details>

### comments mode: enforced comment-only protection

#### blocks body edits but allows adding comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_new("comments", true, "")
assert_false(can_edit_body(prot))
assert_true(can_add_comment(prot))
```

</details>

#### requires no password when password_hash is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_new("comments", true, "")
assert_false(requires_password(prot))
```

</details>

### forms mode: enforced forms-only protection

#### blocks both body edits and comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_new("forms", true, "")
assert_false(can_edit_body(prot))
assert_false(can_add_comment(prot))
```

</details>

### trackedChanges mode: enforced tracked editing

#### allows body edits (tracked) and allows comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_new("trackedChanges", true, "")
assert_true(can_edit_body(prot))
assert_true(can_add_comment(prot))
```

</details>

### non-enforced protection: enforcement off means no restriction

#### allows body edits and comments even in readOnly mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_new("readOnly", false, "")
assert_true(can_edit_body(prot))
assert_true(can_add_comment(prot))
```

</details>

### protection_summary: readable one-line description

#### formats none as just \

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_none()
expect(protection_summary(prot)).to_equal("none")
```

</details>

#### formats enforced readOnly with a password

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_read_only("abc123")
expect(protection_summary(prot)).to_equal("readOnly (enforced, password)")
```

</details>

#### formats enforced protection without a password

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_new("forms", true, "")
expect(protection_summary(prot)).to_equal("forms (enforced)")
```

</details>

#### formats non-enforced protection

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prot = protection_new("comments", false, "")
expect(protection_summary(prot)).to_equal("comments (not enforced)")
```

</details>

### deliberate-fail probe (must be fixed to green before landing)

#### confirms trackedChanges still permits body edits when enforced

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
