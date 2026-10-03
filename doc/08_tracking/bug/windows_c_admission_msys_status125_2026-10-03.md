# Windows C admission rejects successful compile through MSYS status125

Observed2026-10-03 during Item3 canonical bootstrap recovery. Retained Rust producer matched its input hash, but `bootstrap_stage3_windows_runnable_compiler` rejected clang-cl with shell-status125 and a nonempty object. This is not proof of native success: no native exit receipt existed. Recovery cycle1 terminated before Stage2.

The direct `env -i ... clang-cl` route relied on MSYS status. The existing bounded Windows process adapter already records native child status, helper identity, log hash and clean-prefix environment. C admission now uses that adapter on Windows, retains its receipts in `native_probe/c-admission`, and still requires native success plus nonempty object. Non-Windows fallback remains unchanged. No status125 exception or object-only admission was added.

A first isolated adapter probe exposed MSYS conversion of slash-prefixed `/nologo /c /Fo...` arguments before the Python native boundary. Equivalent clang-cl hyphen aliases avoid that conversion. Executable, source, object and PATH are converted to native Windows spelling; INCLUDE/LIB/SDK environment remains explicit. Native timeout30s, log cap1MiB.

Tests-first commit3e5c9263217 added the actual Windows regression. Before implementation it exited127 because the required helper did not exist. After implementation, the regression exited0 and exercised actual valid C compilation with spaced paths, malformed C despite a stale object, absent compiler rejection, and the production selector admission. Both valid and malformed probes checked completed native receipts; malformed native status was nonzero. No mocked compiler or synthetic exit was used.

Evidence remains outside sparse checkout in `C:/dev/simple/.git/worktrees/simple-item3-spec-20261003/item3-bootstrap/recovery-20261003/`: `c-regression-red.log`, `c-regression-green.log`, `c-regression-green/valid.log`, `c-regression-green/invalid.log`, and their process receipt directories. This verifies orchestration only; no pure-Simple feature tests or full CLI admission are claimed. Full bootstrap recovery remains separately bounded.
