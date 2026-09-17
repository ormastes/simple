# Pure-Simple darwin macho binary (c438fee2139) is defective in its own build, not stale - 2026-09-17

- **Status:** OPEN (filed 2026-09-17)
- **Severity:** P1 — the newest pure-Simple macOS binary cannot run specs or programs; blocks every native macOS evidence lane
- **Lane:** macOS bug/todo db sweep 2026-09-17 — `gpu_renderer_processing_metal_native_macos_2026-08-02.md` probe
- **Host:** macOS 25.5.0, Apple M4 (aarch64)
- **Binary:** `bin/release/aarch64-apple-darwin-macho/simple` (Sep-7 build, source snapshot `c438fee2139`)

## Finding

The macho binary has a real Metal implementation linked (distinct
`rt_metal_init` / `rt_metal_is_available` symbols, links Metal.framework), so
it was the candidate for exercising Metal natively. It cannot run anything:

1. **`simple test` SIGSEGVs in runner setup** — null call from
   `daemon_sdk daemon_ensure_running` (confirmed via the 2026-09-12 `.ips`
   crash report; re-measured 2026-09-17).
2. **In-process `simple run` segfaults even on `print("HELLO")`** — a
   compiler/FFI ABI mismatch fires before user code.
3. Default `run` silently delegates to the seed; seed-compiled `.smf` is
   rejected (magic drift).

## Why this is a build defect, not staleness

Both failures were **reproduced against the binary's own Sep-7 source
snapshot** (`c438fee2139`). A stale binary fails against newer source; this
binary fails against its own source — the defects were built into it.

## Consequences

- Every native macOS evidence lane that needs a pure-Simple binary (Metal
  processing backend, crash-handler deploy verification, deployed test-runner
  slots, spipe docgen) stays blocked until the root lane rebuilds and admits a
  source-matched darwin binary.
- Related records: `macos_deployed_test_runner_load_only_greenwash_2026-09-12.md`,
  `macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot_2026-08-31.md`,
  `crash_handler_and_fork_bridge_absent_from_seed_macos_2026-09-06.md`,
  `gpu_renderer_processing_metal_native_macos_2026-08-02.md`.

## Acceptance

- A darwin self-hosted binary built from current source runs
  `simple test <spec>` and `simple run` (in-process mode) without SEGV on
  this host.
- Re-run the gpu_renderer_processing native rows and the wm_metal_glass 5-spec
  battery against it.
