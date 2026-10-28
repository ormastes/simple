# Cached phase2 resolves the resource-scope shell local as a function

Canonical ID: `phase2_resource_scope_shell_shadow_2026_10_28`
Status: OPEN; source workaround active; authoritative DB reconciliation pending.
Owner: compiler local-name/function-value resolution; next admitted compiler rebuild.

After PR #5170 repaired capture pointer/length transport, the native runner still
failed every bounded child launch. LLDB on the existing phase2-built runner showed
`rt_process_run_bounded_tuple` receiving ARM64 instruction bytes as its command.
The stack passed through `_run_with_unix_limits` and `_legacy_process_fallback`.
The local `shell` binding collides with a global function name in this producer.

Evidence: `/tmp/test-runner-refresh-20261028/child-launch.lldb.log` and
`qualification-patched/`. Original source recovery: `74c4f7c879b`.
Producer: existing `stage2-simple-aliasfix` under
`/Users/ormastes/wt/release-phase2-review/build/verify/pure-spl-aliasfix-p2-20261025-02/`.
The compiler is intentionally not rebuilt in this task.

Workaround: rename the `_run_with_unix_limits` local to `limit_shell_path`
and the `_limit_shell` loop local to `candidate_shell_path`. The first native
probe proved the neighboring loop collision as well: no-pid-cap children passed,
but the pid-capped child incorrectly reported that no supported shell existed.
The host has `/bin/bash`; the renamed loop must return that executable.
Its tagged source and this report are committed before native qualification;
the workaround commit is discoverable with `git log -S phase2_resource_scope_shell_shadow_2026_10_28`.
Retirement requires a new admitted producer and an original-name reproducer that
executes real scoped children. A source rename does not fix the compiler.

Prevention: the native capture fixture now covers the runner's scope entry,
pid-capped and ordinary POSIX shells, empty/spaced/quoted/UTF-8 arguments,
stdout/stderr, child exit 7, missing executable, and timeout classification.
The standalone gate verifies all 11 named cases independently of runner status.
Native runner acceptance uses positive, negative and empty BDD, SSpec, plain SPL,
Markdown and source-comment fixtures; all receipts are retained separately.

## Native qualification

Workaround commits: `9fd8fc597a6` (call site) and `75a52c487ae` (selector).
Qualified source: `75a52c487aefa57e0a5a6fc9bd7cda103a40fec4`.
Producer SHA256: `0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`.
The phase2 compiler was not rebuilt. The initial sparse-checkout link failure
(missing counterpart header) and call-site-only 10/11 result remain retained.
After both renames, all 11 native regression cases pass. Probe SHA256:
`ddd6e27f108367b6b2ee10b0de6b18771aa4a88fb7d62b963b97d28669ae2277`.
Luna reviewed the exact source commit without findings.

The native runner built in 195 seconds, peak observed process-tree RSS
7,439,824 KiB, quiescent completion, SHA256:
`ea9972bd35a2023594baa24c2a4e6d37c90dd3702bb8e44c46951e4c3b62b501`.
Receipts and immutable fixture copies/hashes:
`/tmp/runner-limit-shell-evidence-20261028/` (`scope-build.status`,
`scope-check.stdout`, `runner-build.status`, `runner-build.rss.env`,
`qualification-patched/identity.json`, `qualification-patched/rows.json`).
Its 24 positive/negative/empty invocations used the retained Phase1 child;
this mixed-producer run is diagnostic, not phase2 child admission.

Markdown returns expected exits 0/1/1 and pass/fail/no-block results. The four
source-documentation forms (`#`, `##`, `///`, docstring) each produce expected
doctest subresults: green 1 passed, red 1 failed, empty rejected. Standalone
snippets use conditional `panic` assertions; the earlier raw `assert` inputs
were invalid under the retained child and remain preserved in the prior folder.

The normal file route still reports `Resource limit exceeded ()` for BDD,
SSpec, plain SPL and source-comment files, after successfully launching the
child. All 21 non-Markdown commands therefore return 1. Some show the existing
MC/DC compile fallback diagnostic (`struct i64 has no field recorder`). No
positive BDD/SSpec/plain-SPL acceptance or whole comment-command success is
claimed. See `phase2_runner_empty_limit_classification_2026_10_28.md` for the
next blocker. Do not promote this candidate or mark the compiler defect fixed.
