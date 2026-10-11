# Inventory Publication Trace Specification

> Tests covering Inventory transaction diagnostic contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inventory Publication Trace Specification

## Scenarios

### Inventory transaction diagnostic contract

#### accepts bounded hexadecimal attempts and rejects unsafe tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(inventory_trace_token_valid_v1("0123456789abcdef")).to_equal(true)
expect(inventory_trace_token_valid_v1("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")).to_equal(true)
expect(inventory_trace_token_valid_v1("")).to_equal(false)
expect(inventory_trace_token_valid_v1("0123456789abcde")).to_equal(false)
expect(inventory_trace_token_valid_v1("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0")).to_equal(false)
expect(inventory_trace_token_valid_v1("0123456789abcdeF")).to_equal(false)
expect(inventory_trace_token_valid_v1("0123456789abcde\n")).to_equal(false)
expect(inventory_trace_token_valid_v1("0123456789abcde한")).to_equal(false)
expect(inventory_trace_create_v1("")).to_be_nil()
```

</details>

#### replaces unsafe digest fields without admitting them as evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
expect(inventory_trace_digest_v1(digest)).to_equal(digest)
expect(inventory_trace_digest_v1("")).to_equal("")
expect(inventory_trace_digest_v1("private/path\nphase=4")).to_equal("invalid")
val pending = inventory_trace_create_v1("0123456789abcdef")
expect(pending != nil).to_equal(true)
val diagnostic = pending!
diagnostic.begin("private/root", ["src"], false)
diagnostic.captured_pointer("", digest, 3, "private/path\nphase=4")
diagnostic.observed(1, 1, digest, "private/path")
diagnostic.prepared(0, 1, digest)
diagnostic.finish(false, "private/failure", "", -1)
expect(diagnostic.invalid_fields).to_equal(true)
expect(diagnostic.begin_record.contains("private/")).to_equal(false)
expect(diagnostic.observed_record.contains("private/")).to_equal(false)
expect(diagnostic.result_record.contains("private/")).to_equal(false)
expect(diagnostic.begin_record.len() <= 1024).to_equal(true)
expect(diagnostic.observed_record.len() <= 1024).to_equal(true)
expect(diagnostic.prepared_record.len() <= 1024).to_equal(true)
expect(diagnostic.result_record.len() <= 1024).to_equal(true)
expect(diagnostic.result_record.contains("reached=3")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/cache/inventory_publication_trace_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Inventory transaction diagnostic contract.
- Inventory transaction diagnostic contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
