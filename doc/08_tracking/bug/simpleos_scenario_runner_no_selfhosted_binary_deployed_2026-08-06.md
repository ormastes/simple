# Bug: no genuine self-hosted `simple` binary deployed in this environment — scenario runner can never find a runnable compiler

**ID:** simpleos-scenario-runner-no-selfhosted-binary-deployed-2026-08-06
**Domain:** os/simpleos build tooling (`src/os/_QemuRunner/os_build_run.spl`, deployment state)
**Severity:** blocker (for `bin/simple os build`/`os test --scenario=...` end-to-end)
**Filed:** 2026-08-06
**Discovered while verifying:**
`doc/08_tracking/bug/os_build_scenario_runner_5s_compiler_probe_timeout_2026-08-06.md`

## Summary

After fixing the 5s compiler-discovery probe timeout (see the linked bug),
`bin/simple os test --scenario=riscv64-smoke` still fails with:

```
[build][riscv64] phase=tooling FAILED: no runnable pure-Simple compiler
```

but now for a different, orthogonal reason: every candidate path
`_find_simple_binary_for_target` (`src/os/_QemuRunner/os_build_run.spl:477+`)
checks currently resolves to the Rust bootstrap **seed**, not a genuine
self-hosted build:

```
$ bin/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta

$ readlink -f bin/simple
/home/ormastes/dev/pub/simple/release/x86_64-unknown-linux-gnu/simple   # <- also prints the seed warning

$ bin/release/x86_64-unknown-linux-gnu/simple --version                # also seed
```

`_simple_binary_is_valid` (`os_build_run.spl:423-434`) correctly rejects any
candidate whose `--version` output contains `"bootstrap seed only"`, so every
candidate in the search list is rejected before the (now-fixed) native-build
contract probe is ever reached. This gate masks the probe-timeout fix from
end-to-end verification today — it does not indicate anything wrong with that
fix (which was verified directly, in isolation, in the linked bug doc). The
bug here is that no candidate satisfying the design's assumption ("a genuine
self-hosted binary is deployed at one of these paths") currently exists in
this environment.

## Owed verification

Once a genuine self-hosted binary is deployed to one of the candidate paths,
re-run `bin/simple os test --scenario=riscv64-smoke` (or any scenario) and
confirm it gets past `phase=tooling` — that is the end-to-end confirmation the
probe-timeout fix could not get today.

## Two smaller findings from the same investigation

- The probe's exact-string match in `_simple_binary_has_native_build_contract`
  (`Error: invalid --mode '...' (expected dynload or one-binary)`) does not
  match the wording the Rust seed emits for the same condition (`error:
  invalid --mode '...'. Expected dynload or one-binary`, wrapped in a
  "native-build worker exited with code 1" message). Not a bug for a genuine
  self-hosted candidate, whose `.spl` diagnostic sites do match the probe's
  string — but it was only ever exercised against the seed here, never
  confirmed against a real self-hosted candidate.
- `bin/release/x86_64-unknown-linux-gnu/simple` exists on disk (57.8 MB,
  distinct from `release/x86_64-unknown-linux-gnu/simple`) but is absent from
  both `_find_simple_binary` and `_find_simple_binary_for_target`'s candidate
  lists, which only list `bin/release/linux-x86_64/simple`.

## Why this matters

Per `.claude/rules/bootstrap.md` and CLAUDE.md ("Default tooling =
pure-Simple self-hosted binary, not the Rust seed"), the seed is
bootstrap-only and must never be the thing that actually executes
`os build`/`os test`. Right now it cannot even be tried — there is nothing
else to fall back to.

## Suggested fix

Rebuild and redeploy a genuine self-hosted `bin/simple` (`bin/simple build
bootstrap` or the appropriate redeploy path) to `release/x86_64-unknown-linux-gnu/simple`
so it no longer reports itself as a seed. This is a real bootstrap/build task
in its own right (see `feedback_no_bootstrap_unless_essential` — do not do
this reflexively as a side effect of an unrelated fix) and is out of scope for
the probe-timeout fix that surfaced it.

## Related

- `doc/08_tracking/bug/os_build_scenario_runner_5s_compiler_probe_timeout_2026-08-06.md`
  — the probe-timeout bug fixed alongside this discovery.
