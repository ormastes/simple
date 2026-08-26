# Release workflow still rebuilds after a tag

**Status:** Open release blocker
**Owner:** Release CI maintainers

## Evidence

`.github/workflows/release.yml` is still initiated from release-tag state and
contains tolerated/fallback artifact paths. That conflicts with the admitted
candidate and promote-without-rebuild contract implemented by
`src/app/release/policy.spl` and documented in
`doc/07_guide/infra/software_release.md`.

## Unblock condition

Split candidate build/qualification from protected promotion. Promotion must
consume one immutable candidate manifest and exact artifact digests, perform no
build, reject every required fallback, and publish only one exact signed tag.
The replacement workflow needs adversarial tests for stale candidate identity,
changed artifact digest, fallback selection, and rebuild-on-promote.
