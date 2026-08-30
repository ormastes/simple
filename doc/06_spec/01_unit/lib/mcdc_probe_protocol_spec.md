# MC/DC Pinned Probe Protocol — Unit Manual

Executable: `test/01_unit/lib/mcdc_probe_protocol_spec.spl`  
Requirements: REQ-MCDC-SHORT-CIRCUIT-002, REQ-MCDC-DYNAMIC-007  
Status: **unverified** — the self-hosted `bin/simple` runtime is absent in this
worktree, so SPipe generation was not executed.

## Scenarios

The spec checks that static registries remain cold before configuration, bind
owners only during cold setup, and use owner-local fixed storage thereafter. It
then checks dynamic publication/unload retry behavior, observed-only
short-circuit masks, reader pins, prepared-worker publication, compiler-derived
masking, nested decision slots, and separate owner capsules.

Every assertion is a concrete protocol state or bounded record count. None of
these unit scenarios proves emitted static-off code has no symbols or that an
external dynamic aspect executes in a deployed binary.

## Regeneration

```text
bin/simple spipe-docgen test/01_unit/lib/mcdc_probe_protocol_spec.spl --output doc/06_spec --no-index
bin/simple test test/01_unit/lib/mcdc_probe_protocol_spec.spl --mode=interpreter
```
