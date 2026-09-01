# Release Process Hardening Feature Expert

Use `doc/07_guide/infra/software_release.md` for operations and `doc/04_architecture/release_process_hardening.md` for authority boundaries. Implementation lives in `src/app/release/policy.spl` and the release CLI; executable evidence is `test/03_system/app/release/feature/release_process_hardening_spec.spl`.

Preserve isolated sessions, canonical versions, reviewed one-fix beta backports, immutable candidates, promote-not-rebuild, signed exact tags, and non-destructive withdrawal. During beta/bootstrap, bounded discovery may compare exact `main` and release-line snapshots read-only; selection and mutation remain explicit. Forward-port a release-first bug fix to `main` through its own reviewed session and divergence receipt. `main` remains trunk and never tracks the release branch. Do not treat local planning checks as live GitHub/signing/publication evidence.
