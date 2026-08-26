# Software Release Layer Expert

The software-release layer converts canonical version, VCS policy, session, backport, candidate, admission, and artifact facts into fail-closed plans before provider mutation.

Canonical references:

- `doc/07_guide/infra/software_release.md`
- `doc/04_architecture/release_process_hardening.md`
- `release/version.sdn`
- `.spipe/policy/vcs.sdn`
- `src/app/release/policy.spl`

Protected mutation belongs to the lifecycle/integration gateway; compiler admission belongs to bootstrap owners. This layer must not duplicate either boundary or add raw Git/process/runtime shortcuts.
