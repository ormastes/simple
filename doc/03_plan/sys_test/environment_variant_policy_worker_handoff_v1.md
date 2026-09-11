# Environment variant policy worker handoff V1 test plan

- Pure codec: canonical roundtrip of the complete policy collection and source
  receipt, fixed field order, integrity, size bounds, malformed input,
  provenance substitution, and policy/target-sensitive cache identity.
- Application owner: source precedence, one internal argument, exact public
  argv preservation, and missing/duplicate/corrupt rejection.
- Native-build component: parent, shards, worker, and warm receipt use the one
  payload without policy environment rewriting; full and slim workers apply
  the decoded typed collection before source loading.
- Process boundary: parse shards keep selected callable owner/session/generation
  zero because callable sessions are not serializable worker authority.
- Administrator authority: explicitly excluded until an authenticated source
  owner exists; digest integrity receives no authority credit.
- Qualified self-host execution: required before production admission. Seed
  interpreter smoke is diagnostic only.
