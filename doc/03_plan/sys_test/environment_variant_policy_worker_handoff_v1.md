# Environment variant policy worker handoff V1 test plan

- Pure codec: canonical roundtrip, fixed field order, integrity, size bounds,
  malformed input, and policy/target-sensitive cache identity.
- Application owner: source precedence, one internal argument, exact public
  argv preservation, and missing/duplicate/corrupt rejection.
- Native-build component: parent, shards, worker, and warm receipt use the one
  payload without policy environment rewriting.
- Administrator authority: explicitly excluded until an authenticated source
  owner exists; digest integrity receives no authority credit.
- Qualified self-host execution: required before production admission. Seed
  interpreter smoke is diagnostic only.

