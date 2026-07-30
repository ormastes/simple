# Browser Renderer Command Capability Codec

> The SBR2 codec binds each non-ready renderer command to one canonical lowercase capability trailer. This focused scenario proves framing and validation only; entropy, issuance, and renderer lifecycle are separate lanes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Command Capability Codec

The SBR2 codec binds each non-ready renderer command to one canonical lowercase capability trailer. This focused scenario proves framing and validation only; entropy, issuance, and renderer lifecycle are separate lanes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/01_unit/lib/common/web/browser_renderer_command_capability_codec_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The SBR2 codec binds each non-ready renderer command to one canonical
lowercase capability trailer. This focused scenario proves framing and
validation only; entropy, issuance, and renderer lifecycle are separate lanes.

The four named checker functions below contain the complete executable
evidence for the four manual steps.

Requirement trace: REQ-WEB-BROWSER-014, REQ-WEB-BROWSER-018, and
REQ-WEB-BROWSER-020.

## Examples

The scenario encodes one deterministic 16-byte fixture to 32 lowercase
hexadecimal bytes, feeds the wire across every split point, and rejects legacy,
noncanonical, oversized, or truncated inputs. The capability value itself is
never included in an error reason or manual evidence row.

## Scenarios

### Browser renderer command capability codec

#### should fail closed at every SBR2 framing boundary

- Encode the renderer command capability
- Decode the bounded command
- Reject malformed or legacy commands
- Clear capability material


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_renderer_command_capability_encode()
check_renderer_command_capability_decode()
check_renderer_command_capability_rejection()
check_renderer_command_capability_clear()
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
