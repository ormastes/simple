# Const Keys Specification

> Tests covering TemplateKey, TemplateSchema, ConstKeyError, ConstKeyValidator, edit_distance, TemplateAnalysis, TemplateChecker, TemplateInstance, extract_template_keys, validate_template_keys, suggest_key_fix, render_template, Const Keys Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Keys Specification

## Scenarios

### TemplateKey

#### creates required key

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates required key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates required key")
# TemplateKey.required("name", 0)
# key.is_optional == false
pass
```

</details>

#### creates optional key with default

- creates optional key with default


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates optional key with default")
# TemplateKey.optional("name", 0, "default")
# key.is_optional == true
# key.default_value == Some("default")
pass
```

</details>

#### formats required key

- formats required key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats required key")
# key.to_text() == "name"
pass
```

</details>

#### formats optional key

- formats optional key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats optional key")
# key.to_text() == "name? = \"default\""
pass
```

</details>

### TemplateSchema

#### extracts keys from simple template

- extracts keys from simple template


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts keys from simple template")
# TemplateSchema.from_template("Hello {name}!")
# schema.keys.len() == 1
# schema.keys[0].name == "name"
pass
```

</details>

#### extracts multiple keys

- extracts multiple keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts multiple keys")
# TemplateSchema.from_template("{greeting} {name}!")
# schema.keys.len() == 2
pass
```

</details>

#### extracts optional keys

- extracts optional keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts optional keys")
# TemplateSchema.from_template("{name?=World}")
# schema.optional_keys contains "name"
pass
```

</details>

#### handles template with no keys

- handles template with no keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles template with no keys")
# TemplateSchema.from_template("Hello World!")
# schema.keys.is_empty()
pass
```

</details>

#### handles adjacent keys

- handles adjacent keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles adjacent keys")
# TemplateSchema.from_template("{first}{last}")
# schema.keys.len() == 2
pass
```

</details>

#### checks if key exists

- checks if key exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if key exists")
# schema.has_key("name") == true
# schema.has_key("other") == false
pass
```

</details>

#### gets key by name

- gets key by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets key by name")
# schema.get_key("name").?
pass
```

</details>

#### returns all key names

- returns all key names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all key names")
# schema.key_names() == ["greeting", "name"]
pass
```

</details>

#### formats keys for error messages

- formats keys for error messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats keys for error messages")
# schema.format_keys() == "\"greeting\", \"name\""
pass
```

</details>

### ConstKeyError

#### formats unknown key error

- formats unknown key error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats unknown key error")
# ConstKeyError.UnknownKey("usr", ["user"], Some("user"))
# error.to_text() contains "usr" and "user"
pass
```

</details>

#### formats missing key error

- formats missing key error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats missing key error")
# ConstKeyError.MissingKey("name", ["name", "city"])
# error.to_text() contains "Missing required key"
pass
```

</details>

#### formats multiple errors

- formats multiple errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats multiple errors")
# ConstKeyError.MultipleErrors([...])
# error.to_text() contains all error messages
pass
```

</details>

#### identifies errors with suggestions

- identifies errors with suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies errors with suggestions")
# error.has_suggestion() == true when suggestion present
pass
```

</details>

### ConstKeyValidator

#### creates validator for template

- creates validator for template


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates validator for template")
# ConstKeyValidator.for_template("Hello {name}!")
pass
```

</details>

#### validates correct keys

- validates correct keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates correct keys")
# validator.validate(["name"]) == Ok(())
pass
```

</details>

#### rejects unknown keys

- rejects unknown keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown keys")
# validator.validate(["unknown"]) == Err(UnknownKey(...))
pass
```

</details>

#### requires all required keys

- requires all required keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires all required keys")
# Template: "{first} {last}"
# validator.validate(["first"]) == Err(MissingKey("last",...))
pass
```

</details>

#### allows optional keys to be missing

- allows optional keys to be missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows optional keys to be missing")
# Template: "{name?=World}"
# validator.validate([]) == Ok(())
pass
```

</details>

#### finds similar keys for suggestions

- finds similar keys for suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds similar keys for suggestions")
# validator.find_similar_key("usr") == Some("user")
pass
```

</details>

#### returns None for very different keys

- returns None for very different keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for very different keys")
# validator.find_similar_key("xyz") == None
pass
```

</details>

### edit_distance

#### returns 0 for identical strings

- returns 0 for identical strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for identical strings")
# edit_distance("hello", "hello") == 0
pass
```

</details>

#### counts single character difference

- counts single character difference


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts single character difference")
# edit_distance("cat", "bat") == 1
pass
```

</details>

#### counts insertions

- counts insertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts insertions")
# edit_distance("cat", "cats") == 1
pass
```

</details>

#### counts deletions

- counts deletions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts deletions")
# edit_distance("cats", "cat") == 1
pass
```

</details>

#### handles empty strings

- handles empty strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty strings")
# edit_distance("", "abc") == 3
# edit_distance("abc", "") == 3
pass
```

</details>

#### calculates complex differences

- calculates complex differences


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates complex differences")
# edit_distance("kitten", "sitting") == 3
pass
```

</details>

### TemplateAnalysis

#### creates from literal

- creates from literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates from literal")
# TemplateAnalysis.from_literal("Hello {name}!", "line:1")
# analysis.is_const == true
pass
```

</details>

#### creates dynamic analysis

- creates dynamic analysis


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates dynamic analysis")
# TemplateAnalysis.dynamic("line:1")
# analysis.is_const == false
pass
```

</details>

#### checks if can validate

- checks if can validate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if can validate")
# literal.can_validate() == true
# dynamic.can_validate() == false
pass
```

</details>

### TemplateChecker

#### creates empty checker

- creates empty checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty checker")
# TemplateChecker.create()
# checker.has_errors() == false
pass
```

</details>

#### registers templates

- registers templates


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers templates")
# checker.register_template("greeting", analysis)
pass
```

</details>

#### validates with call on registered template

- validates with call on registered template


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates with call on registered template")
# checker.check_with_call("greeting", ["name"], "line:5")
pass
```

</details>

#### records errors for invalid keys

- records errors for invalid keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records errors for invalid keys")
# checker.check_with_call("greeting", ["wrong"], "line:5")
# checker.has_errors() == true
pass
```

</details>

#### warns on unknown template variable

- warns on unknown template variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on unknown template variable")
# checker.check_with_call("unknown", ["key"], "line:5")
# checker.get_warnings().len() > 0
pass
```

</details>

#### warns on dynamic template

- warns on dynamic template


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on dynamic template")
# With dynamic analysis
# checker.get_warnings() contains "Cannot validate"
pass
```

</details>

### TemplateInstance

#### creates valid instance

- creates valid instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates valid instance")
# TemplateInstance.create("Hello {name}!", {"name": "Alice"})
# result.is_ok()
pass
```

</details>

#### fails on missing required key

- fails on missing required key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on missing required key")
# TemplateInstance.create("Hello {name}!", {})
# result.is_err()
pass
```

</details>

#### fails on unknown key

- fails on unknown key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on unknown key")
# TemplateInstance.create("Hello {name}!", {"nam": "Alice"})
# result.is_err()
pass
```

</details>

#### renders template with values

- renders template with values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders template with values")
# instance.render() == "Hello Alice!"
pass
```

</details>

#### uses default for optional keys

- uses default for optional keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses default for optional keys")
# Template: "Hello {name?=World}!"
# instance.render() == "Hello World!"
pass
```

</details>

### extract_template_keys

#### extracts all keys from template

- extracts all keys from template


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts all keys from template")
# extract_template_keys("Welcome {user} to {city}")
# == ["user", "city"]
pass
```

</details>

### validate_template_keys

#### validates correct keys

- validates correct keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates correct keys")
# validate_template_keys("Hello {name}!", ["name"]) == Ok(())
pass
```

</details>

#### rejects incorrect keys

- rejects incorrect keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects incorrect keys")
# validate_template_keys("Hello {name}!", ["wrong"]) is Err
pass
```

</details>

### suggest_key_fix

#### suggests similar key

- suggests similar key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests similar key")
# suggest_key_fix("Hello {user}!", "usr") == Some("user")
pass
```

</details>

#### returns None for no match

- returns None for no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for no match")
# suggest_key_fix("Hello {user}!", "xyz") == None
pass
```

</details>

### render_template

#### renders valid template

- renders valid template


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders valid template")
# render_template("Hello {name}!", {"name": "World"})
# == Ok("Hello World!")
pass
```

</details>

#### fails on invalid keys

- fails on invalid keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on invalid keys")
# render_template("Hello {name}!", {"wrong": "World"})
# is Err
pass
```

</details>

### Const Keys Integration

#### validates complex template

- validates complex template


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates complex template")
# Template: "Welcome {user} to {city} on {date}!"
# Keys: ["user", "city", "date"]
pass
```

</details>

#### suggests fixes for typos

- suggests fixes for typos


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests fixes for typos")
# "Welcome {user} to {citi}"
# Suggests "city" for "citi"
pass
```

</details>

#### handles nested braces in content

- handles nested braces in content


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested braces in content")
# Template with literal braces should work
pass
```

</details>

#### works with empty values

- works with empty values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with empty values")
# {"name": ""} should be valid
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/const_keys_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TemplateKey, TemplateSchema, ConstKeyError, ConstKeyValidator, edit_distance, TemplateAnalysis, TemplateChecker, TemplateInstance, extract_template_keys, validate_template_keys, suggest_key_fix, render_template, Const Keys Integration.
- TemplateKey
- TemplateSchema
- ConstKeyError
- ConstKeyValidator
- edit_distance
- TemplateAnalysis
- TemplateChecker
- TemplateInstance
- extract_template_keys
- validate_template_keys
- suggest_key_fix
- render_template
- Const Keys Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
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

- Canonical SPipe generation for source `fc7264d6d60d4333e914441d9662111c6d497b7eab25ebe6eb99efd6c9a84f5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc7264d6d60d4333e914441d9662111c6d497b7eab25ebe6eb99efd6c9a84f5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc7264d6d60d4333e914441d9662111c6d497b7eab25ebe6eb99efd6c9a84f5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/semantics/const_keys_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/const_keys_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/semantics/const_keys_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/const_keys_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/const_keys_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler/semantics/const_keys_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates required key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/const_keys_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates optional key with default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/const_keys_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats required key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
