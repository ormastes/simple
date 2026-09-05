# Software Release Command

Route stable and prerelease release work through the general software-release skill and `doc/07_guide/infra/software_release.md`. Perform check/plan operations first. Require explicit approval before any external push, signing, publication, ruleset change, or package registry mutation.

During beta/bootstrap, periodically compare exact `main` and `release/X.Y` snapshots read-only. Only an explicitly selected reviewed fix may cross via an isolated backport or forward-port, renewed evidence, divergence receipt, and protected integration authority. Keep `main` as trunk; never make it track or become the release branch.
