# Windows native-all import libraries in the pure-Simple linker

2026-10-04; base `4190684c8f7`; target release/1.0.
Status: source repair `52d43348d7c` and executable intent `f73e8a13155`
independently source-reviewed; no P0/P1 found in this scoped change.
All Simple test execution and native host qualification remain **UNRUN**.

## Observed defect and provenance

The retained diagnostic directory is
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/p2-next20975-cranelift-startup3/`.
Its `collector1/build.log` reports unresolved `PdhAddEnglishCounterW`,
`PdhGetFormattedCounterValue`, `PdhOpenQueryA`, `PdhCollectQueryData`,
`CallNtPowerInformation`, `NetGroupEnum`, `NetApiBufferFree`, and
`GetModuleFileNameExW`, among related imports. The native-all archive contributes
the sysinfo references. No response file was inspected in this investigation.

That attempt used immutable older producer `7a98ce791c33cc7f7091c46a9cf87bad68b40193d0c09a9332da078ced505c91`.
Its proposal already identifies the old producer's missing libraries and a
separate retained-object diagnostic relink policy. This document neither changes
that owner's artifacts nor treats the failure as execution of current Simple
linker source.

Historical repair `0abc0fefa7812789f9ce8f59f7833a541fe40a1c`, merged by PR 2392,
added the four libraries to `src/compiler_rust/common/src/platform/link_config.rs`.
Its existing report is
`doc/08_tracking/bug/windows_native_all_sysinfo_link_libraries_2026-10-04.md`.
Those Rust-specific implementation and validation claims must not be inherited
by the pure-Simple owner. Source inspection finds the same four libraries absent
from `src/compiler/70.backend/linker/_LinkerWrapper/native_all_support.spl`.
This independent source mismatch is the defect repaired by the current lane.

## Unchanged API and selected-runtime contract

Keep the existing archive recognizer and helper signatures:

- `native_all_msvc_support_libraries(inputs)` returns its existing dependencies
  plus `pdh.lib`, `netapi32.lib`, `psapi.lib`, and `powrprof.lib` when an actual
  supported native-all archive filename is present.
- `native_all_gnu_support_args(inputs, os, macos_prefix)` adds `-lpdh`,
  `-lnetapi32`, `-lpsapi`, and `-lpowrprof` only in its `windows-mingw` branch
  under the same archive-selection gate.
- Core-only inputs remain empty. Similar filenames, import-library lookalikes,
  and suffixes rejected by `native_all_input_present` remain rejected.
- Linux, macOS and FreeBSD results remain unchanged. No other default runtime,
  target, linker selection or unrelated platform library table is modified.

The MSVC helper is already consumed by native external linking and internal PE
support-library discovery. Shared-link consumers also reuse the owner. Add the
dependencies there, not independently to each caller's unconditional Windows
list. The source change supplies library names; it does not invent exports,
replace actual SDK import libraries, or claim successful native execution.
An SDK installation missing a required library must still produce a real error.

## Acceptance and ownership

Initial executable intent `f73e8a13155` updates the existing
`test/01_unit/compiler/linker/native_link_hardening_spec.spl` before source
implementation. The new scenario is "adds each Windows native-all resource
dependency once for either archive spelling"; its shared step is "Resolve SDK
libraries through the actual native-all support owners". Existing runtime,
filename and non-Windows controls are strengthened. No new helper API is added.

Before source edits, author tests calling the actual helpers with literal input
archives and independently named expected libraries. Require all four names for
MSVC and MinGW; require no added names for core-only and rejected lookalike
inputs. Check non-Windows outputs against their existing policy, including
retained Vulkan force-link arguments where applicable. Do not copy stale exact
arrays from older tests and silently remove existing arguments to make them pass.

These policy tests do not prove a Windows linker consumed the names. Eventual
native evidence must use real SDK libraries and actual references to the four
API families, retain the link invocation/artifact identity, and execute the
result on a qualified Windows host. MinGW needs its own toolchain evidence.
All five-host item4 requirements and the separate runtime recovery remain open.

Runtime owns the shared source helper; acceptance owns focused executable tests
and their mirrored manual; research owns this design, canonical acceptance
linkage and independent final review; root owns integration and landing.
Separate worktrees; sidecars N/A. No existing bootstrap/cache owner is modified.

The final production diff adds one row to each Windows library array; recognizer,
callers and non-Windows arms are unchanged. Tests require each dependency exactly
once despite repeated selected inputs, preserve existing support names, and
exercise both archive spellings. Source review is not observed RED/GREEN or a
link/run receipt.
