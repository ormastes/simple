# Test runner: child exit-1 mislabels files; repo-path spec expectation failures not propagated

Date: 2026-07-02
Status: open
Severity: P1 (gate trustworthiness)
Found by: W3 lane agent (proved with negative controls)

## Symptom 1 — child process exit poisons file status

Any spec that legitimately spawns a child which exits 1 (e.g. asserting a
fail-closed tool flag) marks the whole file
`FAILED ... Error: Process exited with code 1` even when every
expectation passed — while the summary can simultaneously say all passed.
Minimal repro: one `process_run_timeout("node", ["-e","process.exit(1)"])`.

## Symptom 2 — expectation failures silently pass for repo-path system specs

For system specs under the repo test tree, `expect(...)` failures inside
`it` blocks are NOT propagated to the summary. Negative control: a
deliberately wrong pin in famous_site_production_probe_spec.spl still
reported `Passed: 4`. The SAME file copied to an out-of-repo path fails
correctly.

## Impact

Green runs of repo system specs (including the Chrome-parity corpus and
probe gates) are not trustworthy on their own. Until fixed, verify gates
via their underlying tools (e.g.
`node tools/electron-shell/verify_famous_site_production_probe.js` and
its fail-closed flags) in addition to `bin/simple test`.
