# Const Keys Specification

> <details>

<!-- sdn-diagram:id=const_keys_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=const_keys_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

const_keys_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=const_keys_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Const Keys Specification

## Scenarios

### TemplateKey

#### creates required key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateKey.required("name", 0)
# key.is_optional == false
pass
```

</details>

#### creates optional key with default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateKey.optional("name", 0, "default")
# key.is_optional == true
# key.default_value == Some("default")
pass
```

</details>

#### formats required key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# key.to_text() == "name"
pass
```

</details>

#### formats optional key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# key.to_text() == "name? = \"default\""
pass
```

</details>

### TemplateSchema

#### extracts keys from simple template

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateSchema.from_template("Hello {name}!")
# schema.keys.len() == 1
# schema.keys[0].name == "name"
pass
```

</details>

#### extracts multiple keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateSchema.from_template("{greeting} {name}!")
# schema.keys.len() == 2
pass
```

</details>

#### extracts optional keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateSchema.from_template("{name?=World}")
# schema.optional_keys contains "name"
pass
```

</details>

#### handles template with no keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateSchema.from_template("Hello World!")
# schema.keys.is_empty()
pass
```

</details>

#### handles adjacent keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateSchema.from_template("{first}{last}")
# schema.keys.len() == 2
pass
```

</details>

#### checks if key exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# schema.has_key("name") == true
# schema.has_key("other") == false
pass
```

</details>

#### gets key by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# schema.get_key("name").?
pass
```

</details>

#### returns all key names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# schema.key_names() == ["greeting", "name"]
pass
```

</details>

#### formats keys for error messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# schema.format_keys() == "\"greeting\", \"name\""
pass
```

</details>

### ConstKeyError

#### formats unknown key error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ConstKeyError.UnknownKey("usr", ["user"], Some("user"))
# error.to_text() contains "usr" and "user"
pass
```

</details>

#### formats missing key error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ConstKeyError.MissingKey("name", ["name", "city"])
# error.to_text() contains "Missing required key"
pass
```

</details>

#### formats multiple errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ConstKeyError.MultipleErrors([...])
# error.to_text() contains all error messages
pass
```

</details>

#### identifies errors with suggestions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# error.has_suggestion() == true when suggestion present
pass
```

</details>

### ConstKeyValidator

#### creates validator for template

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ConstKeyValidator.for_template("Hello {name}!")
pass
```

</details>

#### validates correct keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# validator.validate(["name"]) == Ok(())
pass
```

</details>

#### rejects unknown keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# validator.validate(["unknown"]) == Err(UnknownKey(...))
pass
```

</details>

#### requires all required keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Template: "{first} {last}"
# validator.validate(["first"]) == Err(MissingKey("last",...))
pass
```

</details>

#### allows optional keys to be missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Template: "{name?=World}"
# validator.validate([]) == Ok(())
pass
```

</details>

#### finds similar keys for suggestions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# validator.find_similar_key("usr") == Some("user")
pass
```

</details>

#### returns None for very different keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# validator.find_similar_key("xyz") == None
pass
```

</details>

### edit_distance

#### returns 0 for identical strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# edit_distance("hello", "hello") == 0
pass
```

</details>

#### counts single character difference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# edit_distance("cat", "bat") == 1
pass
```

</details>

#### counts insertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# edit_distance("cat", "cats") == 1
pass
```

</details>

#### counts deletions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# edit_distance("cats", "cat") == 1
pass
```

</details>

#### handles empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# edit_distance("", "abc") == 3
# edit_distance("abc", "") == 3
pass
```

</details>

#### calculates complex differences

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# edit_distance("kitten", "sitting") == 3
pass
```

</details>

### TemplateAnalysis

#### creates from literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateAnalysis.from_literal("Hello {name}!", "line:1")
# analysis.is_const == true
pass
```

</details>

#### creates dynamic analysis

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateAnalysis.dynamic("line:1")
# analysis.is_const == false
pass
```

</details>

#### checks if can validate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# literal.can_validate() == true
# dynamic.can_validate() == false
pass
```

</details>

### TemplateChecker

#### creates empty checker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateChecker.create()
# checker.has_errors() == false
pass
```

</details>

#### registers templates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.register_template("greeting", analysis)
pass
```

</details>

#### validates with call on registered template

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_with_call("greeting", ["name"], "line:5")
pass
```

</details>

#### records errors for invalid keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_with_call("greeting", ["wrong"], "line:5")
# checker.has_errors() == true
pass
```

</details>

#### warns on unknown template variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# checker.check_with_call("unknown", ["key"], "line:5")
# checker.get_warnings().len() > 0
pass
```

</details>

#### warns on dynamic template

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With dynamic analysis
# checker.get_warnings() contains "Cannot validate"
pass
```

</details>

### TemplateInstance

#### creates valid instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateInstance.create("Hello {name}!", {"name": "Alice"})
# result.is_ok()
pass
```

</details>

#### fails on missing required key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateInstance.create("Hello {name}!", {})
# result.is_err()
pass
```

</details>

#### fails on unknown key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TemplateInstance.create("Hello {name}!", {"nam": "Alice"})
# result.is_err()
pass
```

</details>

#### renders template with values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# instance.render() == "Hello Alice!"
pass
```

</details>

#### uses default for optional keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Template: "Hello {name?=World}!"
# instance.render() == "Hello World!"
pass
```

</details>

### extract_template_keys

#### extracts all keys from template

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# extract_template_keys("Welcome {user} to {city}")
# == ["user", "city"]
pass
```

</details>

### validate_template_keys

#### validates correct keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# validate_template_keys("Hello {name}!", ["name"]) == Ok(())
pass
```

</details>

#### rejects incorrect keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# validate_template_keys("Hello {name}!", ["wrong"]) is Err
pass
```

</details>

### suggest_key_fix

#### suggests similar key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# suggest_key_fix("Hello {user}!", "usr") == Some("user")
pass
```

</details>

#### returns None for no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# suggest_key_fix("Hello {user}!", "xyz") == None
pass
```

</details>

### render_template

#### renders valid template

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# render_template("Hello {name}!", {"name": "World"})
# == Ok("Hello World!")
pass
```

</details>

#### fails on invalid keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# render_template("Hello {name}!", {"wrong": "World"})
# is Err
pass
```

</details>

### Const Keys Integration

#### validates complex template

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Template: "Welcome {user} to {city} on {date}!"
# Keys: ["user", "city", "date"]
pass
```

</details>

#### suggests fixes for typos

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "Welcome {user} to {citi}"
# Suggests "city" for "citi"
pass
```

</details>

#### handles nested braces in content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Template with literal braces should work
pass
```

</details>

#### works with empty values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# {"name": ""} should be valid
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/const_keys_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
