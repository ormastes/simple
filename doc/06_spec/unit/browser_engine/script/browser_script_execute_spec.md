# Browser Script Execute Specification

## Scenarios

### hardened browser script execution

#### executes only deterministic literal console logs without host subprocesses

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><script>console.log('hello'); console.log(\"world\")</script></body></html>"
val result = execute_scripts_in_html(html)

expect(result.scripts_collected).to_equal(1)
expect(result.scripts_executed).to_equal(1)
expect(result.scripts_denied).to_equal(0)
expect(result.console_output).to_contain("hello")
expect(result.console_output).to_contain("world")
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### denies Node and host escape APIs before execution

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<script>require('fs').readFileSync('/etc/passwd');</script><script>process.env.OPENAI_API_KEY</script><script>host.shell('id')</script>"
val result = execute_scripts_in_html(html)

expect(result.scripts_collected).to_equal(3)
expect(result.scripts_executed).to_equal(0)
expect(result.scripts_denied).to_equal(3)
expect(result.diagnostics).to_contain("module loader access denied")
expect(result.diagnostics).to_contain("ambient environment access denied")
expect(result.diagnostics).to_contain("host shell access denied")
```

</details>

#### denies external scripts and unsupported script types fail closed

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<script src='https://example.com/app.js'></script><script type='text/simple'>stdout_write('bad')</script>"
val result = execute_scripts_in_html(html)

expect(result.scripts_collected).to_equal(2)
expect(result.scripts_executed).to_equal(0)
expect(result.scripts_denied).to_equal(2)
expect(result.diagnostics).to_contain("external script src denied: https://example.com/app.js")
expect(result.diagnostics).to_contain("unsupported script type denied: text/simple")
```

</details>

#### propagates denied browser JavaScript diagnostics through rendering

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><title>Script Gate</title></head><body><h1>Visible</h1><script>fetch('https://example.com')</script></body></html>"
val result = render_html_to_pixels_with_scripts(html, 64, 64)

expect(result.ok).to_equal(true)
expect(result.title).to_equal("Script Gate")
expect(result.scripts_collected).to_equal(1)
expect(result.scripts_executed).to_equal(0)
expect(result.scripts_denied).to_equal(1)
expect(result.diagnostics).to_contain("network access denied")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/browser_engine/script/browser_script_execute_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hardened browser script execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

