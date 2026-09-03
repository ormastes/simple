# Native-Build Darwin Action Identity Production Path

- Executable: `test/02_integration/app/macos_native_action_identity_production_spec.spl`
- Requirements: `MBH-REQ-001`, `MBH-REQ-002`, `MBH-REQ-004`, `MBH-REQ-009`
- Evidence class: executable slow integration definition; no native result is embedded.

## Scenarios

- publishes and admits the real CLI writer output, then rejects a changed SDK
- rejects a non-Mach-O runtime artifact through the production success funnel
- rejects a runtime artifact with the wrong Mach-O slice

## Freshness

The requirement IDs and scenario titles mirror the executable source. Native
qualification remains blocked until an admitted native runner executes it.
