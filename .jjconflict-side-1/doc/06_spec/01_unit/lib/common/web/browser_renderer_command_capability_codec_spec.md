# Opt-in Browser Renderer Command Capability Codec

> The explicit opt-in SBR2 helpers frame one canonical lowercase capability trailer without changing the production SBR1 encoder, decoder, resequencer, or their callers. This scenario proves only isolated framing, canonical validation, bounds, and decoder cleanup.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opt-in Browser Renderer Command Capability Codec

The explicit opt-in SBR2 helpers frame one canonical lowercase capability trailer without changing the production SBR1 encoder, decoder, resequencer, or their callers. This scenario proves only isolated framing, canonical validation, bounds, and decoder cleanup.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/01_unit/lib/common/web/browser_renderer_command_capability_codec_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The explicit opt-in SBR2 helpers frame one canonical lowercase capability
trailer without changing the production SBR1 encoder, decoder, resequencer, or
their callers. This scenario proves only isolated framing, canonical
validation, bounds, and decoder cleanup.

The four named checker functions below contain the complete executable
evidence for the four manual steps.

The opt-in wire is not a causal capability boundary. Entropy, staged issuance,
parent/worker correlation, nested schema migration, secret retirement, and
production requirement completion remain outside this scenario.

## Examples

The scenario preserves a successful SBR1 round trip, then encodes one
deterministic 16-byte fixture to 32 lowercase hexadecimal bytes, feeds only the
opt-in SBR2 decoder across every split point, and rejects malformed,
noncanonical, oversized, or truncated opt-in inputs.

## Scenarios

### Browser renderer command capability codec

#### should fail closed at every SBR2 framing boundary

- Encode the opt-in renderer command capability
- Decode the bounded opt-in command
- Reject malformed opt-in capability commands
- Clear bounded opt-in decoder state


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_renderer_command_capability_encode()
check_renderer_command_capability_decode()
check_renderer_command_capability_rejection()
check_renderer_capability_decoder_cleanup()
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

- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>
