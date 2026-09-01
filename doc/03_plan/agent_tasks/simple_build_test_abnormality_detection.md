# Agent Tasks: Simple Build/Test Abnormality Detection

| Lane | Ownership | Depends on | Review |
|---|---|---|---|
| A | observed-process API, wait4/rusage, signals | none | root |
| B | Linux cgroup v2 scope | A | root |
| C | Windows Job Object + macOS fallback | A | root; native-host evidence retained |
| D | test-runner resource evidence/limits | A, B/C contracts | root |
| E | SDN run schemas/cohort/baseline records | shared value model | root |
| F | compiler phase spans/work counters | shared value model | root |
| G | MAD/paired/EWMA/CUSUM decisions | E | root |
| H | aspect/cache identity and counters | E, F | root |
| I | PR/nightly policy and diagnostics | D, F, G | root |
| J | SSpec, manuals, classification/regression verification | all | root final reviewer |

Merge owner: root Codex agent. Final reviewer and generated-manual reviewer: root Codex agent at normal/highest capability. Sidecars are read-only research reviewers unless explicitly reassigned. Shared interface/helper names are fixed in `.spipe/simple-build-test-abnormality-detection/state.md`.

Unavailable Windows/macOS native rows remain active. Owner: platform lane C. Unblock: prepared native host with current branch and admitted pure-Simple binary. Resume: run the focused platform resource-scope spec and record binary/path/hash, OS, command, exit, and raw evidence artifact; then request root final review.
