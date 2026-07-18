# Feature: SimpleOS Startup GOT and mmap Hardening

## Raw Request
$sp_dev impl and harden,
check got is used only on simple os baremetal config and not used in simple os on host to use file system to launch
check executable startup. early file parsing still works and loading with mmap on linux and simple os(similar).

## Task Type
bug

## Refined Goal
Harden executable startup so GOT-specific loading is selected only for SimpleOS bare-metal targets, hosted SimpleOS launches through the filesystem path, and early argument/file parsing plus mapped executable loading work on Linux and the equivalent SimpleOS path.

## Acceptance Criteria
- AC-1: The authoritative target/configuration decision enables GOT-specific startup only for SimpleOS bare-metal builds and a focused check rejects GOT selection for hosted SimpleOS builds.
- AC-2: A hosted SimpleOS executable launch resolves and reads the requested executable through its filesystem loader rather than the bare-metal GOT payload path.
- AC-3: Startup parses direct file arguments early enough that an executable or script supplied as the first launch input is identified before heavyweight command initialization, with existing direct-file behavior preserved.
- AC-4: Linux startup maps eligible executable input with the existing mmap-backed loader, preserves byte/length/error semantics, and has a runnable check that discriminates mmap from ordinary buffered reading.
- AC-5: SimpleOS startup uses its target-equivalent mapped/file-backed executable loading path with the same observable byte/length/error contract, with runnable target or source-contract evidence that does not substitute host `bin/simple` for in-guest behavior.
- AC-6: Focused startup evidence covers bare-metal GOT selection, hosted filesystem selection, early file parsing, Linux mmap loading, and the SimpleOS-equivalent loading path without placeholder assertions or silent fallback.
- AC-7: Required startup SPipe manual and operator-facing startup/SimpleOS guide content reflects the final behavior; executable specs remain under `test/`, generated manuals under `doc/06_spec`, and the generated-spec layout guard reports zero misplaced `.spl` files.
- AC-8: Compiler/core checks and the working/staged direct-runtime-access guards pass once for the final touched scope, with unrelated concurrent work excluded from the completion claim.

## Scope Exclusions
No new loader abstraction, file format, or generalized virtual-memory API unless current owner paths cannot express the required target split.

## Cooperative Review
N/A: this lane should converge on one existing startup/loader owner boundary; concurrent repository sessions already own broad compiler, runtime, and SimpleOS files, so adding sidecar edits would increase collision risk. The primary agent remains merge owner and final reviewer, and the existing canonical `step("...")`/startup helper vocabulary will be reused.

## Phase
dev-done

## Log
- dev: Created state file with 8 acceptance criteria (type: bug).

## Research Summary

### Existing Code
- `src/app/startup/launch_metadata.spl:33-130` already owns pure launch-kind, argv, mmap/VFS-cache, and dynlib policy.
- `src/compiler_rust/driver/src/main.rs:1007-1050` runs early file detection and prefetch before normal CLI dispatch; `early_startup.rs` preserves the remaining argv.
- `src/compiler_rust/driver/src/prefetch.rs:151-188` maps hosted Unix files with `MAP_PRIVATE` and Linux read-ahead advice.
- `src/os/kernel/ipc/syscall_process.spl:766-818` resolves filesystem bytes before consulting the bare-metal resident binary table.
- `src/os/kernel/loader/disk_launch_manifest.spl:57-73` deliberately returns `nil` so known app paths fall through to ELF/SMF filesystem loading.
- `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` covers direct argv and mmap but incorrectly prefers Rust seed binaries over `bin/simple`.

### Reusable Modules
- Reuse `StartupLaunchPlan`; add only an explicit executable-source decision.
- Reuse the existing startup and SimpleOS specs rather than create a parallel harness.

### Domain Notes
- Hosted Linux mmap and SimpleOS VFS read-ahead have different mechanisms but the same startup contract: filesystem bytes are authoritative and resident fallback cannot masquerade as a loaded executable.

### Open Questions
- NONE

<!-- sdn-diagram:id=simpleos-startup-source -->
```sdn
startup_source:
  hosted_linux: early_argv -> filesystem_mmap -> executable
  hosted_simpleos: early_argv -> filesystem -> executable
  baremetal_simpleos: filesystem_first -> resident_got_fallback
```

## Requirements
- REQ-1 (AC-1, AC-2): Startup policy exposes `filesystem` for hosted Linux/SimpleOS and `baremetal_got` only for explicit SimpleOS bare-metal metadata — area: `src/app/startup/`.
- REQ-2 (AC-3): Direct file argv remains normalized exactly once before normal command dispatch — area: `src/app/io/`, Rust early startup.
- REQ-3 (AC-4, AC-5): Hosted Linux mmap and SimpleOS VFS/read-ahead preserve exact file bytes and fail closed — area: runtime file IO and `src/os/kernel/loader/`.
- REQ-4 (AC-6..AC-8): Focused specs/manuals and runtime-access/layout guards provide non-placeholder evidence without claiming unrelated dirty work.

## Architecture
- Decision A-1: Extend the existing pure `StartupLaunchPlan`; do not add a loader abstraction.
- Decision A-2: `target_abi=simpleos-baremetal` is the explicit resident-GOT selector; every other target uses filesystem source.
- Decision A-3: Keep mmap/VFS prewarm as cache strategy orthogonal to executable source.
- Public surface: `launch_metadata_for_simpleos_baremetal_path(path)` and `StartupLaunchPlan.executable_source`.

## Phase
arch-done

## Log
- research: Reused five startup/loader owners and derived four requirements; no external dependency needed.
- arch: Selected one policy-field extension and existing specs; no new loader layer.

## Specs
- `test/03_system/app/simpleos/feature/simple_app_startup_spec.spl` covers explicit bare-metal GOT versus hosted filesystem/mmap source and SimpleOS VFS prewarm.
- `test/03_system/app/simple/feature/simple_app_startup_spec.spl` covers Linux/host filesystem mmap policy.
- `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` covers direct early argv parsing and exact mmap reads with the self-hosted binary.
- Generated manuals: matching paths under `doc/06_spec/`; docgen reported 0 stubs for all three.
- Manual shape: the host/bare-metal decision is a visible two-step primary scenario; existing cache/hover matrices remain supporting scenarios.

## Implementation
- `src/app/startup/launch_metadata.spl`: added `StartupLaunchPlan.executable_source`; default is `filesystem`, and only `target_abi=simpleos-baremetal` selects `baremetal_got`.
- `src/app/startup/launch_meta_check.spl`: added explicit `--simpleos-host` and `--simpleos-baremetal`; legacy `--simpleos` remains the bare-metal alias.
- Startup perf evidence now selects `bin/simple` first and launches the file directly instead of measuring the heavier `simple run` command surface.
- Runtime boundary: no new `rt_*` imports or wrappers; existing facades/owners reused. `runtime_need=N/A`, `chosen_path=reuse-facade`, `rejected_shortcuts=new loader abstraction, hosted resident fallback, Rust-seed test substitution`.

## Refactor
- Updated startup architecture, system-test plan, compiler application guide, SimpleOS dev guide, and all three generated manuals.
- No overlay wiki files referenced this startup policy; `.spipe/core/` remained untouched.
- Cooperative review remains `N/A` because concurrent sessions own adjacent compiler/kernel files; primary agent reviewed the bounded policy/manual diff.

## Phase
refactor-done

## Log
- spec: Extended three existing specs; 29 examples passed with 0 failures and direct mmap/startup evidence passed 2/0.
- implement: Added explicit executable-source policy and config selection without a new loader layer.
- refactor: Removed stale command/fallback wording and refreshed generated manuals with 0 stubs.

## Verification Report
- PASS AC-1/AC-2: executable `launch-meta` probes reported `baremetal_got` only for `--simpleos-baremetal` and `filesystem|cache=mmap` for `--simpleos-host`.
- PASS AC-2/AC-5: `executable_source_vfs_spec.spl` passed 14/0, including exact VFS/initramfs bytes and filesystem aliases.
- PASS AC-3/AC-4: `startup_argparse_mmap_perf_spec.spl` passed 2/0 through the self-hosted direct-file path; exact mmap content and latency bounds passed.
- PASS AC-6: Simple startup policy passed 18/0; SimpleOS startup/prefetch passed 9/0; no placeholder/stub patterns found in lane files.
- PASS AC-7: all three generated manuals reported 0 stubs; generated-spec layout search returned no `.spl` files.
- PASS AC-8: scoped diff check, numbered-artifact working/staged guards, SPipe command wiring, direct-runtime working/staged guards, and scoped strict workspace-root guard passed.
- WARN global workspace-root audit: 402 pre-existing/unrelated manifest violations across the shared checkout; the strict path-file audit for this lane passed and none of the reported global paths were created by this implementation.
- WARN focused two-file `bin/simple check`: reported `All checks passed (1 file(s))` before external termination; executable specs and both direct launch-meta probes compiled and ran the final sources successfully, so no repeat was issued under the runaway guard.

STATUS: PASS

## Phase
verify-done

## Log
- verify: Focused startup/VFS suite passed 43 examples with 0 failures; policy probes and all scoped guards passed.
