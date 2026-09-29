# Verification: Simple 2D / Skia / RenderDoc hardening

Date: 2026-09-26. Selection: feature C, evidence N2. Scope: the selected
requirements and this rendering lane's current source, tests, and plans.
This is a bounded readiness audit, not a new runtime or device test.

| Phase | Result | Evidence |
|---|---|---|
| Scope | WARN | Local/domain research, final requirements, architecture, design, system plan and agent-task plan exist. The worktree has concurrent changes; no combined commit is admitted. No feature-specific knowledge-selection receipt was located by the scoped path search. |
| SPipe | FAIL | Requirement-tagged source specs and mirrored manuals exist; a scoped placeholder scan found no `pass_todo`, vacuous `expect(true).to_equal(true)`, `# TODO`, or `# FIXME`. The new/changed specs have no trusted Simple execution or successful `spipe-docgen` zero-stub receipt. |
| Implementation | FAIL | Case 02 Web projection, Engine2D affine coverage, Skia private-v3 candidate, analytic oracle, and pair runner are source candidates. Pinned Skia compilation, submitted-matrix provenance and physical pixels remain absent. GUI input is source-qualified with a pinned font, but the upstream Skia provider still rejects text. |
| Requirements | FAIL | REQ-2D-001 through 006 have trace tags in focused tests, but REQ-2D-005 lacks admitted native build/device evidence and REQ-2D-006 lacks the planned `31-latin-shaping` runner scene and completed GUI input pixels. No executable `.spl` specs were found under `doc/06_spec` in the scoped layout search. |
| NFR | FAIL | NFR-2D-002 requires a physical Linux Vulkan device; none was supplied or run. Case 02's pinned oracle and tolerance have no two-backend capture. The isolated verifier's retained `renderdoc_test_runner.exit` records `native_build_exit=1`; its link log identifies a Rust bootstrap seed and names unresolved `_rt_cuda_*` and `_rt_vulkan_*` symbols on arm64. The retained core C archive has no `runtime_dynload.o`. This is a failed seed-based attempt, not a trustworthy self-hosted result. The three-cycle verifier cap is reached; this audit did not retry it. |
| Docs | WARN | Plans and design state the current block. The GUI input manual describes source-only evidence. Generated-manual quality and broader guide freshness cannot be accepted without the verifier/docgen gate. |

The numbered-artifact guard passed for `--working` and `--staged` with zero
classified paths. Earlier working/staged direct-env guard passes were retained;
they were not rerun.

After this audit, the optional Skia build path gained a Git-dependency
attestation helper and a larger runner receipt bound for its checkout manifest.
The helper passed a synthetic clean/dirty/disabled/revision-mismatch Git test.
The changed Simple runner source has no trusted compile or runtime result, so
this does not change the FAIL status.
The candidate reader now hashes the exact no-follow byte buffer that it
compares, closing the prior hash-then-read replacement window; this edit is
also source-only pending the same trusted runner gate.

Mac continuation on 2026-09-27: Clang compiled
`tools/upstream-skia-ganesh-vulkan/draw_payload_v3_validate_spec.c` with
`-std=c11 -Wall -Wextra -Werror -pedantic`, and the resulting native CPU
contract executable exited 0. This covers the private v3 shape validator's
positive and malformed/extreme-value cases; it does not compile Ganesh or
qualify Vulkan. The remaining physical work is tracked in
`doc/08_tracking/todo/simple_2d_skia_renderdoc_linux_n2_2026-09-27.md`.
The same Mac host has an Apple M4 GPU and `system_profiler SPDisplaysDataType`
reports `Metal: Supported`, but `vulkaninfo --summary` failed before instance
creation: MoltenVK 1.4.1 reported `VK_ERROR_INCOMPATIBLE_DRIVER` because Metal
was unavailable to this process, and the loader found no usable driver. A
separate Swift Metal probe, with its module cache relocated into `/private/tmp`,
returned `no Metal device` from `MTLCreateSystemDefaultDevice()`. Therefore no
Mac Vulkan backend or capture was executed in this session; the Mac live-evidence
runner needs a process with actual Metal device access. The failure is an
environment preflight, not evidence of a renderer pass or renderer defect.
Further host checks found an Aqua login session and an active `AGXAcceleratorG16G`
in I/O Registry. This command environment denied `ps` and `/usr/bin/log show`
with sandbox errors, so the exact Metal access denial cannot be inspected here.
The hardware is present; a GPU-accessible command process is still required.
The newer September 18 Mac `simple` binary crashed with exit `-11` during a
single deliberately failing matcher control, before any test case result.
Its rendering test output is therefore also inadmissible.
Its single bounded `check src/app/test/vulkan_2d_qualification` attempt exited
`1` after 43.29 seconds with 1,262 diagnostic lines; the captured tail contains
generic compiler warnings rather than a scoped first error. No syntax PASS is
claimed from that attempt, and it was not retried.

Kimi continuation on 2026-09-27 (preflight only, no status change): the
Metal/MoltenVK device admission succeeded in this process — Apple M4,
MoltenVK 1.4.1, canonical Homebrew ICD, receipt at
`build/tmp/macos_vulkan_2d_preflight_2026-09-27/preflight.env`, report at
`doc/09_report/macos_vulkan_2d_preflight_2026-09-27.md`. The Stage-2 environment
blocker from 2026-09-26 was a sandbox denial, not a device defect. The
retained `_rt_cuda_*`/`_rt_vulkan_*` mini-build link failure was diagnosed:
the hand-assembled core C archive omitted `runtime_dynload.o` (source at
`src/runtime/runtime_dynload.c`; the canonical core-c-bootstrap bundle
includes it). The full-bootstrap trust-root lane required two environment
corrections (llvm-config on PATH; `SIMPLE_BOOTSTRAP_RUST_LLVM=0` for the
llvm-sys-18 vs host-LLVM-23 pin); a separate session owns the canonical
bootstrap lane from a clean snapshot worktree, so the duplicate Kimi-lane
bootstrap was stopped after fingerprint to keep CPU/disk for that lane.

Kimi continuation on 2026-09-27 (evening, evidence update only — **STATUS
unchanged: FAIL**): the optional upstream Skia macOS lane is now complete as
far as possible without a physical Linux host. Pinned checkout
`35d5edfa0d50984c22ff94f5438c31e0db12c6f8` obtained with 45 attested Git
dependencies (`verify-skia-deps.py` gained annotated-tag peeling); the
provider built deterministically twice (`build-macos.shs` added: attest-gated
sync, in-tree Vulkan headers, CoreServices, and a MoltenVK portability
fix — `VK_KHR_portability_enumeration` — in `provider.cpp`); case01/case06
readbacks match their pinned independent oracles exactly on the admitted
MoltenVK device; the device/driver UUID identity export verifies against the
preflight receipt; fail-closed fault behaviors and default-build v3 rejection
are device-verified (19/19). Case02 v3 ran with full submitted-matrix
provenance (corner error 0.000434 px vs 0.125 bound) but 4 of 914 edge pixels
exceed the predeclared 16-delta tolerance — recorded, not fudged, in
`doc/08_tracking/bug/skia_case02_edge_tolerance_exceedance_2026-09-27.md`.
The bootstrap lane reached an admitted Stage-2 candidate (`7620bf8f…`) but
the phase-verification matrix is blocked by the owner-decision bug
`doc/08_tracking/bug/macos_stage2_compiler_cli_build_host_gpu_link_2026-09-27.md`
(host-gpu full-CLI provider set on Darwin); Stage 3/deploy, the Engine2D
live-evidence run, GUI/Web spec execution, and Linux N2 all remain gated on
that decision or on physical Linux hardware.

Next gates: run `scripts/check/check-macos-vulkan-2d-live-evidence.shs` once
from a Mac process that can enumerate a Metal device and pass its MoltenVK
preflight. Deploy a working pure-Simple self-hosted binary (`bin/simple` is
currently a symlink to the Rust bootstrap seed), establish a trusted
failing-assertion control, then run the changed
specs and docgen once. Build the exact pinned Skia revision on an admitted
physical Linux Vulkan host, capture both backends, and verify the selected
case/GUI pixels. Keep the 48-case corpus rows `not-run` until their own gates
pass.

**STATUS: FAIL** — release and physical N2 qualification are not admitted.
