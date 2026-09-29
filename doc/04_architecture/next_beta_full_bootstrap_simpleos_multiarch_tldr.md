# Next Beta Full Bootstrap and SimpleOS Multiarch — TLDR

Purpose: publish `v1.0.0-beta2` only after real full-bootstrap and SimpleOS
x86_64/AArch64/RISC-V64 evidence succeeds.

Decision: harden `.github/workflows/release.yml` as one fail-closed artifact
DAG. Reuse existing bootstrap scripts, target/scenario catalogs, QEMU gates,
memory gates, payload checker, and mission-critical checker. Add no release
framework, target registry, or MDSOC capsule.

Flow:

```text
identity + matrices + memory + whole tests
  -> strict artifact/receipt preflight
  -> GitHub prerelease
  -> query and verify actual GitHub release/assets
```

Critical rules:

- tag equals `v$(cat VERSION)`;
- no Rust-seed, stale-binary, source-only, or `continue-on-error` success;
- each SimpleOS architecture boots and runs its embedded compiler;
- every artifact has a receipt and SHA-256;
- mission-critical gate reports `release_blockers=none`;
- first green run establishes same-runner RSS/time baselines; later regression
  limit is 10%;
- prereleases never update mutable `latest`.

Next paths: `.github/workflows/release.yml`,
`scripts/bootstrap/bootstrap-from-scratch.sh`,
`src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl`, and
`scripts/check/check-simpleos-mission-critical-release.shs`.
