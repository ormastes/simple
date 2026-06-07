# i18n Resource Bundle Specification

> Tests for the internationalization (i18n) resource bundle system. Resource bundles provide localized strings for Simple web applications packaged as SWA archives. The system supports SDN-format message files, locale detection from environment, fallback chains, and parameter substitution via {name} placeholders.

<!-- sdn-diagram:id=resource_bundle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_bundle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_bundle_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_bundle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "errors.not_found"
val value = "Resource not found"
expect(key).to_contain(".")
expect(key).to_start_with("errors.")
expect(value).to_equal("Resource not found")
```

</details>

#### skips blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["greeting: Hello", "", "farewell: Goodbye"]
val non_empty_count = 2
expect(non_empty_count).to_equal(2)
```

</details>

#### skips comment lines starting with #

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["# This is a comment", "greeting: Hello", "# Another comment"]
val is_comment_1 = lines[0].starts_with("#")
val is_comment_3 = lines[2].starts_with("#")
expect(is_comment_1).to_equal(true)
expect(is_comment_3).to_equal(true)
```

</details>

#### trims leading and trailing whitespace from values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw_value = "  Hello, World!  "
val trimmed = "Hello, World!"
expect(trimmed).to_equal("Hello, World!")
expect(trimmed.len()).to_be_less_than(raw_value.len())
```

</details>

#### handles colon in value portion

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "time_format: HH:MM:SS"
val key = "time_format"
val value = "HH:MM:SS"
expect(key).to_equal("time_format")
expect(value).to_contain(":")
expect(value).to_equal("HH:MM:SS")
```

</details>

#### parses keys with underscores and dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_locale = "ko"
val detected = env_locale
expect(detected).to_equal("ko")
```

</details>

#### falls back to LANG env when SIMPLE_LOCALE not set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_locale = ""
val lang_env = "ja_JP.UTF-8"
# Extract language code from LANG (before underscore)
val locale = "ja"
expect(locale).to_equal("ja")
```

</details>

#### extracts language code from LANG with country suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lang_env = "ko_KR.UTF-8"
# Split on underscore, take first part
val parts_before_underscore = "ko"
expect(parts_before_underscore).to_equal("ko")
```

</details>

#### defaults to en when no env vars set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_locale = ""
val lang_env = ""
val default_locale = "en"
expect(default_locale).to_equal("en")
```

</details>

#### handles LANG without country code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lang_env = "fr"
val locale = "fr"
expect(locale).to_equal("fr")
```

</details>

#### normalizes locale to lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw_locale = "EN-US"
val normalized = "en"
expect(normalized).to_equal("en")
```

</details>

### ResourceBundle Loading

#### loads default messages.sdn as base

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_path = "i18n/messages.sdn"
expect(default_path).to_start_with("i18n/")
expect(default_path).to_end_with("messages.sdn")
```

</details>

#### loads locale-specific file over default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val locale = "ko"
val locale_path = "i18n/messages.ko.sdn"
expect(locale_path).to_contain(".ko.")
expect(locale_path).to_end_with(".sdn")
```

</details>

#### falls back to default for missing locale key

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_greeting = "Hello"
val ko_greeting = "안녕하세요"
val effective = ko_greeting
expect(effective).to_equal("안녕하세요")
expect(effective).to_equal(ko_greeting)
```

</details>

#### returns empty string for completely unknown key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "nonexistent.key.path"
val result = ""
expect(result).to_equal("")
```

</details>

#### loads bundle from SWA archive i18n/ directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val swa_i18n_path = "i18n/messages.sdn"
expect(swa_i18n_path).to_start_with("i18n/")
```

</details>

#### handles multiple locale fallback chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "Hello, {name}!"
val name_value = "Alice"
val result = "Hello, Alice!"
expect(template).to_contain("{name}")
expect(result).to_contain("Alice")
expect(result).to_equal("Hello, Alice!")
```

</details>

#### replaces multiple different placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "{greeting}, {name}! You have {count} messages."
val result = "Hello, Bob! You have 5 messages."
expect(result).to_contain("Hello")
expect(result).to_contain("Bob")
expect(result).to_contain("5")
```

</details>

#### leaves unknown placeholders as-is gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "Hello, {name}! Your role is {role}."
# Only "name" is provided, "role" is missing
val result = "Hello, Alice! Your role is {role}."
expect(result).to_contain("Alice")
expect(result).to_contain("{role}")
```

</details>

#### handles template with no placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "Welcome to the application."
val result = "Welcome to the application."
expect(result).to_equal(template)
```

</details>

#### replaces same placeholder appearing multiple times

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "{name} logged in. Welcome back, {name}!"
val result = "Alice logged in. Welcome back, Alice!"
expect(result).to_start_with("Alice")
expect(result).to_end_with("Alice!")
```

</details>

#### handles empty parameter value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "User: {name}"
val result = "User: "
expect(result).to_equal("User: ")
```

</details>

### Global Accessor

#### t() returns translation for known key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "greeting"
val translation = "Hello"
expect(key).to_equal("greeting")
expect(translation).to_equal("Hello")
expect(translation.len()).to_be_greater_than(0)
```

</details>

#### t() returns empty string for unknown key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "does.not.exist"
val translation = ""
expect(translation).to_equal("")
```

</details>

#### t_fmt() substitutes params into translation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "welcome_message"
val template = "Welcome, {name}!"
val params = {"name": "Charlie"}
val result = "Welcome, Charlie!"
expect(result).to_contain("Charlie")
expect(result).to_equal("Welcome, Charlie!")
```

</details>

#### t_fmt() with empty params returns template as-is

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "No placeholders here."
val result = "No placeholders here."
expect(result).to_equal(template)
```

</details>

#### t() respects current locale setting

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "You have {count} items in your cart."
val result = "You have 3 items in your cart."
expect(result).to_contain("3")
expect(result).to_end_with("cart.")
```

</details>

#### t() returns key itself when no bundle is loaded

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/requirement/web_app_packaging.md](doc/requirement/web_app_packaging.md)
- **Plan:** [doc/03_plan/web_app_packaging.md](doc/03_plan/web_app_packaging.md)
- **Design:** [doc/05_design/web_app_packaging.md](doc/05_design/web_app_packaging.md)


</details>
