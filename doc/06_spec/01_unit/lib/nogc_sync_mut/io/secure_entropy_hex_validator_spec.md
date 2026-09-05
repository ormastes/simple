# secure_entropy_hex_validator_spec

> Validates only the allocation-free command-capability hex policy seam. A valid candidate is exactly 32 lowercase hexadecimal ASCII bytes and is not all zero. This does not claim platform CSPRNG execution, secret generation, renderer protocol integration, or production capability admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# secure_entropy_hex_validator_spec

Validates only the allocation-free command-capability hex policy seam. A valid candidate is exactly 32 lowercase hexadecimal ASCII bytes and is not all zero. This does not claim platform CSPRNG execution, secret generation, renderer protocol integration, or production capability admission.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/01_unit/lib/nogc_sync_mut/io/secure_entropy_hex_validator_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates only the allocation-free command-capability hex policy seam. A valid
candidate is exactly 32 lowercase hexadecimal ASCII bytes and is not all zero.
This does not claim platform CSPRNG execution, secret generation, renderer
protocol integration, or production capability admission.

## Syntax

`secure_entropy_hex_valid(candidate)` returns a boolean and does not log,
normalize, retain, or copy the candidate.

## Example

The scenario accepts one exact lowercase candidate, then rejects uppercase,
nonhex, all-zero, 31-byte, and 33-byte encodings.

**Requirements:** doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md
**Plan:** doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md
**Design:** doc/05_design/simple_web_browser_engine_production_hardening.md
**Research:** doc/01_research/local/simple_web_browser_engine_production_hardening.md

## Scenarios

### Secure capability entropy hex validation

#### should accept only one nonzero lowercase 16-byte value

- Accept exact lowercase capability entropy
   - Expected: secure_entropy_hex_valid("0123456789abcdef0123456789abcdef") is true
- Reject uppercase and nonhex capability entropy
   - Expected: secure_entropy_hex_valid("0123456789abcdef0123456789abcdeF") is false
   - Expected: secure_entropy_hex_valid("0123456789abcdef0123456789abcdeg") is false
- Reject all-zero capability entropy
   - Expected: secure_entropy_hex_valid("00000000000000000000000000000000") is false
- Reject capability entropy outside the exact length
   - Expected: secure_entropy_hex_valid("0123456789abcdef0123456789abcde") is false
   - Expected: secure_entropy_hex_valid("0123456789abcdef0123456789abcdef0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept exact lowercase capability entropy")
expect(secure_entropy_hex_valid("0123456789abcdef0123456789abcdef")).to_equal(true)

step("Reject uppercase and nonhex capability entropy")
expect(secure_entropy_hex_valid("0123456789abcdef0123456789abcdeF")).to_equal(false)
expect(secure_entropy_hex_valid("0123456789abcdef0123456789abcdeg")).to_equal(false)

step("Reject all-zero capability entropy")
expect(secure_entropy_hex_valid("00000000000000000000000000000000")).to_equal(false)

step("Reject capability entropy outside the exact length")
expect(secure_entropy_hex_valid("0123456789abcdef0123456789abcde")).to_equal(false)
expect(secure_entropy_hex_valid("0123456789abcdef0123456789abcdef0")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>
