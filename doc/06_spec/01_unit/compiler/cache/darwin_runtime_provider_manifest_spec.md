# Darwin Runtime Provider Manifest

- Executable: `test/01_unit/compiler/cache/darwin_runtime_provider_manifest_spec.spl`
- Requirements: `MBH-REQ-002`, `MBH-REQ-004`, `MBH-REQ-009`
- Evidence class: executable SPipe definition; no execution result is embedded.

## Scenarios

- keeps paths receipt-only while binding ordered artifact content
- rehashes live artifact bytes instead of trusting the receipt digest
- binds artifact order with unambiguous digest framing
- records archive members and changes identity when member bytes change
- binds archive member ordering
- does not mistake an ordinary double-underscore BSD member for metadata
- rejects malformed archive header trailers and numeric fields
- rejects missing archive padding and fat headers without a real slice
- rejects malformed non-target and overlapping fat slices

## Freshness

The requirement IDs and scenario titles mirror the executable source. No
native or runtime PASS is claimed.
