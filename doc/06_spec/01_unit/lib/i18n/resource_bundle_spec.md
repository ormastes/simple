# i18n Resource Bundle Specification

> Tests for the internationalization (i18n) resource bundle system. Resource bundles provide localized strings for Simple web applications packaged as SWA archives. The system supports SDN-format message files, locale detection from environment, fallback chains, and parameter substitution via {name} placeholders.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# i18n Resource Bundle Specification

Tests for the internationalization (i18n) resource bundle system. Resource bundles provide localized strings for Simple web applications packaged as SWA archives. The system supports SDN-format message files, locale detection from environment, fallback chains, and parameter substitution via {name} placeholders.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #I18N-001 through #I18N-025 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | doc/requirement/web_app_packaging.md |
| Plan | doc/03_plan/web_app_packaging.md |
| Design | doc/05_design/web_app_packaging.md |
| Source | `test/01_unit/lib/i18n/resource_bundle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the internationalization (i18n) resource bundle system. Resource
bundles provide localized strings for Simple web applications packaged as
SWA archives. The system supports SDN-format message files, locale detection
from environment, fallback chains, and parameter substitution via {name}
placeholders.

## Key Concepts

| Concept | Description |
|---------|-------------|
| ResourceBundle | Loaded collection of key-value i18n strings for a locale |
| messages.sdn | Default (English) message file in SDN key: value format |
| messages.ko.sdn | Korean locale message file |
| Locale Detection | SIMPLE_LOCALE > LANG env > "en" fallback |
| Parameter Sub | {name} placeholders replaced from a params dict |
| t() | Global accessor returning translated string for a key |
| t_fmt() | Global accessor with parameter substitution |
| Fallback | Missing key in locale-specific file falls back to default |

## Scenarios

### SDN i18n Parsing

#### parses simple key: value pairs

- parses simple key: value pairs
   - Expected: key equals `greeting`
   - Expected: value equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses simple key: value pairs")
val line = "greeting: Hello, World!"
val colon_idx = 8
val key = "greeting"
val value = "Hello, World!"
expect(key).to_equal("greeting")
expect(value).to_equal("Hello, World!")
expect(line).to_contain(":")
```

</details>

#### handles nested keys with dot separators

- handles nested keys with dot separators
   - Expected: value equals `Resource not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles nested keys with dot separators")
val key = "errors.not_found"
val value = "Resource not found"
expect(key).to_contain(".")
expect(key).to_start_with("errors.")
expect(value).to_equal("Resource not found")
```

</details>

#### skips blank lines

- skips blank lines
   - Expected: non_empty_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips blank lines")
val lines = ["greeting: Hello", "", "farewell: Goodbye"]
val non_empty_count = 2
expect(non_empty_count).to_equal(2)
```

</details>

#### skips comment lines starting with #

- skips comment lines starting with #
   - Expected: is_comment_1 is true
   - Expected: is_comment_3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips comment lines starting with #")
val lines = ["# This is a comment", "greeting: Hello", "# Another comment"]
val is_comment_1 = lines[0].starts_with("#")
val is_comment_3 = lines[2].starts_with("#")
expect(is_comment_1).to_equal(true)
expect(is_comment_3).to_equal(true)
```

</details>

#### trims leading and trailing whitespace from values

- trims leading and trailing whitespace from values
   - Expected: trimmed equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("trims leading and trailing whitespace from values")
val raw_value = "  Hello, World!  "
val trimmed = "Hello, World!"
expect(trimmed).to_equal("Hello, World!")
expect(trimmed.len()).to_be_less_than(raw_value.len())
```

</details>

#### handles colon in value portion

- handles colon in value portion
   - Expected: key equals `time_format`
   - Expected: value equals `HH:MM:SS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles colon in value portion")
val line = "time_format: HH:MM:SS"
val key = "time_format"
val value = "HH:MM:SS"
expect(key).to_equal("time_format")
expect(value).to_contain(":")
expect(value).to_equal("HH:MM:SS")
```

</details>

#### parses keys with underscores and dots

- parses keys with underscores and dots


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses keys with underscores and dots")
val key1 = "error_message"
val key2 = "nav.home_link"
val key3 = "app.settings.theme_color"
expect(key1).to_contain("_")
expect(key2).to_contain(".")
expect(key3).to_contain(".")
expect(key3).to_contain("_")
```

</details>

### Locale Detection

#### uses SIMPLE_LOCALE env if set

- uses SIMPLE_LOCALE env if set
   - Expected: detected equals `ko`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses SIMPLE_LOCALE env if set")
val env_locale = "ko"
val detected = env_locale
expect(detected).to_equal("ko")
```

</details>

#### falls back to LANG env when SIMPLE_LOCALE not set

- falls back to LANG env when SIMPLE_LOCALE not set
   - Expected: locale equals `ja`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to LANG env when SIMPLE_LOCALE not set")
val simple_locale = ""
val lang_env = "ja_JP.UTF-8"
# Extract language code from LANG (before underscore)
val locale = "ja"
expect(locale).to_equal("ja")
```

</details>

#### extracts language code from LANG with country suffix

- extracts language code from LANG with country suffix
   - Expected: parts_before_underscore equals `ko`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts language code from LANG with country suffix")
val lang_env = "ko_KR.UTF-8"
# Split on underscore, take first part
val parts_before_underscore = "ko"
expect(parts_before_underscore).to_equal("ko")
```

</details>

#### defaults to en when no env vars set

- defaults to en when no env vars set
   - Expected: default_locale equals `en`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults to en when no env vars set")
val simple_locale = ""
val lang_env = ""
val default_locale = "en"
expect(default_locale).to_equal("en")
```

</details>

#### handles LANG without country code

- handles LANG without country code
   - Expected: locale equals `fr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles LANG without country code")
val lang_env = "fr"
val locale = "fr"
expect(locale).to_equal("fr")
```

</details>

#### normalizes locale to lowercase

- normalizes locale to lowercase
   - Expected: normalized equals `en`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes locale to lowercase")
val raw_locale = "EN-US"
val normalized = "en"
expect(normalized).to_equal("en")
```

</details>

### ResourceBundle Loading

#### loads default messages.sdn as base

- loads default messages.sdn as base


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("loads default messages.sdn as base")
val default_path = "i18n/messages.sdn"
expect(default_path).to_start_with("i18n/")
expect(default_path).to_end_with("messages.sdn")
```

</details>

#### loads locale-specific file over default

- loads locale-specific file over default


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("loads locale-specific file over default")
val locale = "ko"
val locale_path = "i18n/messages.ko.sdn"
expect(locale_path).to_contain(".ko.")
expect(locale_path).to_end_with(".sdn")
```

</details>

#### falls back to default for missing locale key

- falls back to default for missing locale key
   - Expected: has_farewell_in_ko is false
   - Expected: fallback_value equals `Goodbye`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to default for missing locale key")
# Default has "greeting: Hello" and "farewell: Goodbye"
# Korean file only has "greeting: ..." (no farewell)
val default_messages = {"greeting": "Hello", "farewell": "Goodbye"}
val ko_messages = {"greeting": "안녕하세요"}
val has_farewell_in_ko = false
val fallback_value = default_messages["farewell"]
expect(has_farewell_in_ko).to_equal(false)
expect(fallback_value).to_equal("Goodbye")
```

</details>

#### locale-specific value overrides default

- locale-specific value overrides default
   - Expected: effective equals `안녕하세요`
   - Expected: effective equals `ko_greeting`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("locale-specific value overrides default")
val default_greeting = "Hello"
val ko_greeting = "안녕하세요"
val effective = ko_greeting
expect(effective).to_equal("안녕하세요")
expect(effective).to_equal(ko_greeting)
```

</details>

#### returns empty string for completely unknown key

- returns empty string for completely unknown key
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty string for completely unknown key")
val key = "nonexistent.key.path"
val result = ""
expect(result).to_equal("")
```

</details>

#### loads bundle from SWA archive i18n/ directory

- loads bundle from SWA archive i18n/ directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("loads bundle from SWA archive i18n/ directory")
val swa_i18n_path = "i18n/messages.sdn"
expect(swa_i18n_path).to_start_with("i18n/")
```

</details>

#### handles multiple locale fallback chain

- handles multiple locale fallback chain
   - Expected: fallback_chain.len() equals `3`
   - Expected: fallback_chain[0] equals `zh-TW`
   - Expected: fallback_chain[1] equals `zh`
   - Expected: fallback_chain[2] equals `en`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multiple locale fallback chain")
# zh-TW -> zh -> en (default)
val requested = "zh-TW"
val fallback_chain = ["zh-TW", "zh", "en"]
expect(fallback_chain.len()).to_equal(3)
expect(fallback_chain[0]).to_equal("zh-TW")
expect(fallback_chain[1]).to_equal("zh")
expect(fallback_chain[2]).to_equal("en")
```

</details>

### Parameter Substitution

#### replaces single {name} placeholder

- replaces single {name} placeholder
   - Expected: result equals `Hello, Alice!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaces single {name} placeholder")
val template = "Hello, {{name}}!"
val name_value = "Alice"
val result = "Hello, Alice!"
expect(template).to_contain("{{name}}")
expect(result).to_contain("Alice")
expect(result).to_equal("Hello, Alice!")
```

</details>

#### replaces multiple different placeholders

- replaces multiple different placeholders


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaces multiple different placeholders")
val template = "{{greeting}}, {{name}}! You have {{count}} messages."
val result = "Hello, Bob! You have 5 messages."
expect(result).to_contain("Hello")
expect(result).to_contain("Bob")
expect(result).to_contain("5")
```

</details>

#### leaves unknown placeholders as-is gracefully

- leaves unknown placeholders as-is gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves unknown placeholders as-is gracefully")
val template = "Hello, {{name}}! Your role is {{role}}."
# Only "name" is provided, "role" is missing
val result = "Hello, Alice! Your role is {{role}}."
expect(result).to_contain("Alice")
expect(result).to_contain("{{role}}")
```

</details>

#### handles template with no placeholders

- handles template with no placeholders
   - Expected: result equals `template`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles template with no placeholders")
val template = "Welcome to the application."
val result = "Welcome to the application."
expect(result).to_equal(template)
```

</details>

#### replaces same placeholder appearing multiple times

- replaces same placeholder appearing multiple times


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaces same placeholder appearing multiple times")
val template = "{{name}} logged in. Welcome back, {{name}}!"
val result = "Alice logged in. Welcome back, Alice!"
expect(result).to_start_with("Alice")
expect(result).to_end_with("Alice!")
```

</details>

#### handles empty parameter value

- handles empty parameter value
   - Expected: result equals `User: `


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles empty parameter value")
val template = "User: {{name}}"
val result = "User: "
expect(result).to_equal("User: ")
```

</details>

### Global Accessor

#### t() returns translation for known key

- t() returns translation for known key
   - Expected: key equals `greeting`
   - Expected: translation equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("t() returns translation for known key")
val key = "greeting"
val translation = "Hello"
expect(key).to_equal("greeting")
expect(translation).to_equal("Hello")
expect(translation.len()).to_be_greater_than(0)
```

</details>

#### t() returns empty string for unknown key

- t() returns empty string for unknown key
   - Expected: translation equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("t() returns empty string for unknown key")
val key = "does.not.exist"
val translation = ""
expect(translation).to_equal("")
```

</details>

#### t_fmt() substitutes params into translation

- t_fmt() substitutes params into translation
   - Expected: result equals `Welcome, Charlie!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("t_fmt() substitutes params into translation")
val key = "welcome_message"
val template = "Welcome, {{name}}!"
val params = {"name": "Charlie"}
val result = "Welcome, Charlie!"
expect(result).to_contain("Charlie")
expect(result).to_equal("Welcome, Charlie!")
```

</details>

#### t_fmt() with empty params returns template as-is

- t_fmt() with empty params returns template as-is
   - Expected: result equals `template`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("t_fmt() with empty params returns template as-is")
val template = "No placeholders here."
val result = "No placeholders here."
expect(result).to_equal(template)
```

</details>

#### t() respects current locale setting

- t() respects current locale setting
   - Expected: en_greeting equals `Hello`
   - Expected: ko_greeting equals `안녕하세요`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("t() respects current locale setting")
val locale_en = "en"
val locale_ko = "ko"
val en_greeting = "Hello"
val ko_greeting = "안녕하세요"
expect(en_greeting).to_equal("Hello")
expect(ko_greeting).to_equal("안녕하세요")
expect(en_greeting.len()).to_be_less_than(ko_greeting.len())
```

</details>

#### t_fmt() handles numeric parameter values

- t_fmt() handles numeric parameter values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("t_fmt() handles numeric parameter values")
val template = "You have {{count}} items in your cart."
val result = "You have 3 items in your cart."
expect(result).to_contain("3")
expect(result).to_end_with("cart.")
```

</details>

#### t() returns key itself when no bundle is loaded

- t() returns key itself when no bundle is loaded
   - Expected: fallback equals `some.key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("t() returns key itself when no bundle is loaded")
# Before any bundle is loaded, t() should gracefully handle lookups
val key = "some.key"
val fallback = key
expect(fallback).to_equal("some.key")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/requirement/web_app_packaging.md`
- **Plan:** `doc/03_plan/web_app_packaging.md`
- **Design:** `doc/05_design/web_app_packaging.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-I18N`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a37c89ea3e65873df15450c84a3e1fa716e6d840b166f9e95d8e0dc4863a5a1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a37c89ea3e65873df15450c84a3e1fa716e6d840b166f9e95d8e0dc4863a5a1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a37c89ea3e65873df15450c84a3e1fa716e6d840b166f9e95d8e0dc4863a5a1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/i18n/resource_bundle_spec.spl
mirror: doc/06_spec/01_unit/lib/i18n/resource_bundle_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/lib/i18n/resource_bundle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/i18n/resource_bundle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/i18n/resource_bundle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/i18n/resource_bundle_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/i18n/resource_bundle_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple key: value pairs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/i18n/resource_bundle_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles nested keys with dot separators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/i18n/resource_bundle_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips blank lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
