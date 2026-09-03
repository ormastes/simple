# Versioned Plugin Identity Values

- Executable: `test/01_unit/lib/common/plugin/iface_id_spec.spl`
- Requirements: `KPM-REQ-002`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution result is embedded.

## Scenarios

- preserves interface identity fields by value
- preserves parameter schema version and presence bits by value
- preserves typed extension identity and canonical payload by value
- copy-on-write payload mutation does not change the source value

## Freshness

The requirement IDs and scenario titles mirror the executable source. No
runtime PASS is claimed.
