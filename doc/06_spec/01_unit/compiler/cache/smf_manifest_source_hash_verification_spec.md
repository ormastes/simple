# SMF Manifest Source-Hash Verification

- Executable: `test/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.spl`
- Evidence class: executable SPipe definition; no runtime PASS is embedded.

## Scenarios

- rejects a recorded source hash that differs from live source bytes;
- rejects the zero-hash sentinel for matching or empty content;
- rejects unreadable live source content;
- round-trips MC/DC policy through the current manifest schema;
- rejects legacy rows instead of inventing policy defaults; and
- rejects legacy manifests before mutation or promotion.

## Selected Policy

The checked reader admits only the current schema and ABI v1 identity. Legacy
schemas remain explicit rejection evidence and cannot authorize cache reuse.

## Evidence Status

- Structural source/manual audit: **PASS**.
- SPipe runtime: **BLOCKED** — the admitted `bin/simple` lacks `test`; no
  synthetic runtime PASS is claimed.
