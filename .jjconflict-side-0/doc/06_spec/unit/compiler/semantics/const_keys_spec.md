# Const Keys Tests

> Compile-time template key validation: schema extraction from `{{key}}` /

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Keys Tests

Compile-time template key validation: schema extraction from `{{key}}` /

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/const_keys_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Compile-time template key validation: schema extraction from `{{key}}` /
`{{key?=default}}` templates, validation of provided keys, typo suggestions via
edit distance, and rendering of template instances.

## Scenarios

### TemplateKey

#### creates required key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val key = TemplateKey.required("name", 0)
expect(key.is_optional).to_equal(false)
expect(key.name).to_equal("name")
```

</details>

#### creates optional key with default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val key = TemplateKey.optional("name", 0, "default")
expect(key.is_optional).to_equal(true)
```

</details>

#### formats required and optional keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(TemplateKey.required("name", 0).to_text()).to_equal("name")
expect(TemplateKey.optional("name", 0, "dflt").to_text()).to_contain("name?")
```

</details>

### TemplateSchema

#### extracts keys from simple template

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val schema = TemplateSchema.from_template("Hello {{name}}!")
expect(schema.keys.len()).to_equal(1)
expect(schema.keys[0].name).to_equal("name")
```

</details>

#### extracts multiple and adjacent keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(TemplateSchema.from_template("{{greeting}} {{name}}!").keys.len()).to_equal(2)
expect(TemplateSchema.from_template("{{first}}{{last}}").keys.len()).to_equal(2)
```

</details>

#### extracts optional keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val schema = TemplateSchema.from_template("{{name?=World}}")
expect(schema.optional_keys.len()).to_equal(1)
expect(schema.optional_keys[0]).to_equal("name")
```

</details>

#### handles template with no keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val schema = TemplateSchema.from_template("Hello World!")
expect(schema.keys.is_empty()).to_equal(true)
expect(schema.format_keys()).to_equal("(no keys)")
```

</details>

#### checks key existence and names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val schema = TemplateSchema.from_template("{{greeting}} {{name}}!")
expect(schema.has_key("name")).to_equal(true)
expect(schema.has_key("other")).to_equal(false)
expect(schema.get_key("name") != nil).to_equal(true)
expect(schema.key_names()).to_equal(["greeting", "name"])
expect(schema.format_keys()).to_equal("\"greeting\", \"name\"")
```

</details>

### ConstKeyValidator

#### validates correct keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val validator = ConstKeyValidator.for_template("Hello {{name}}!")
expect(validator.validate(["name"]).is_ok()).to_equal(true)
```

</details>

#### rejects unknown keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val validator = ConstKeyValidator.for_template("Hello {{name}}!")
expect(validator.validate(["unknown"]).is_ok()).to_equal(false)
```

</details>

#### requires all required keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val validator = ConstKeyValidator.for_template("{{first}} {{last}}")
expect(validator.validate(["first"]).is_ok()).to_equal(false)
```

</details>

#### allows optional keys to be missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val validator = ConstKeyValidator.for_template("{{name?=World}}")
expect(validator.validate([]).is_ok()).to_equal(true)
```

</details>

#### finds similar keys for suggestions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val validator = ConstKeyValidator.for_template("Hello {{user}}!")
expect(validator.find_similar_key("usr")).to_equal("user")
expect(validator.find_similar_key("xyz")).to_equal(nil)
```

</details>

### edit_distance

#### returns 0 for identical strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(edit_distance("hello", "hello")).to_equal(0)
```

</details>

#### counts single substitution, insertion, deletion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(edit_distance("cat", "bat")).to_equal(1)
expect(edit_distance("cat", "cats")).to_equal(1)
expect(edit_distance("cats", "cat")).to_equal(1)
```

</details>

#### handles empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(edit_distance("", "abc")).to_equal(3)
expect(edit_distance("abc", "")).to_equal(3)
```

</details>

#### calculates complex differences

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(edit_distance("kitten", "sitting")).to_equal(3)
```

</details>

### Convenience functions

#### extracts all keys from template

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(extract_template_keys("Welcome {{user}} to {{city}}")).to_equal(["user", "city"])
```

</details>

#### validates and rejects keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(validate_template_keys("Hello {{name}}!", ["name"]).is_ok()).to_equal(true)
expect(validate_template_keys("Hello {{name}}!", ["wrong"]).is_ok()).to_equal(false)
```

</details>

#### suggests similar key and returns nil for no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(suggest_key_fix("Hello {{user}}!", "usr")).to_equal("user")
expect(suggest_key_fix("Hello {{user}}!", "xyz")).to_equal(nil)
```

</details>

### TemplateInstance

#### renders template with values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val result = TemplateInstance.create("Hello {{name}}!", {"name": "Alice"})
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().render()).to_equal("Hello Alice!")
```

</details>

#### uses default for optional keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val result = TemplateInstance.create("Hello {{name?=World}}!", {})
expect(result.unwrap().render()).to_equal("Hello World!")
```

</details>

#### fails on missing or unknown key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(TemplateInstance.create("Hello {{name}}!", {}).is_ok()).to_equal(false)
expect(TemplateInstance.create("Hello {{name}}!", {"nam": "Alice"}).is_ok()).to_equal(false)
```

</details>

### render_template

#### renders valid template

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val r = render_template("Hello {{name}}!", {"name": "World"})
expect(r.is_ok()).to_equal(true)
expect(r.unwrap()).to_equal("Hello World!")
```

</details>

#### fails on invalid keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
expect(render_template("Hello {{name}}!", {"wrong": "World"}).is_ok()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
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

- Canonical SPipe generation for source `e2e17c08e524f20126633a6b0f677553cbc6db2264fc185b60a80957c5f157a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e2e17c08e524f20126633a6b0f677553cbc6db2264fc185b60a80957c5f157a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e2e17c08e524f20126633a6b0f677553cbc6db2264fc185b60a80957c5f157a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/unit/compiler/semantics/const_keys_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/const_keys_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/const_keys_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/const_keys_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/const_keys_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/compiler/semantics/const_keys_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/semantics/const_keys_spec.spl:21:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'creates required key' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/semantics/const_keys_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'creates optional key with default' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/semantics/const_keys_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'formats required and optional keys' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/semantics/const_keys_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'extracts keys from simple template' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
