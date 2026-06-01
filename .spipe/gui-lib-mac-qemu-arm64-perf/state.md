# Feature: gui-lib-mac-qemu-arm64-perf

## Raw Request
$sp_dev check gui lib sanity and perf on mac host, simple os on qemu arm 64. with metal accelerated. already most optimization done you may need check bug and drawing inconsistency. however you need to check perf and capture compares. pure simple impl must optimized and perf. research local and web first and make agent teams detail tasks planes.

## Task Type
code-quality

## Refined Goal
Validate and harden the Simple GUI library across macOS host and SimpleOS QEMU ARM64 Metal-accelerated paths with reproducible sanity, performance, and visual-capture comparison evidence, then produce detailed agent task plans for remaining bug, drawing-consistency, and pure-Simple optimization work.

## Acceptance Criteria
- AC-1: Local research identifies the current GUI library, renderer, capture, SimpleOS QEMU ARM64, Metal acceleration, and performance harness code paths with existing related docs and tests.
- AC-2: Domain research cites current external evidence for macOS Metal-backed acceleration, QEMU ARM64 display/GPU constraints, visual capture comparison practice, and GUI performance measurement.
- AC-3: Requirement and NFR option files exist with selectable alternatives, including pros, cons, and effort estimates, without auto-selecting final requirements.
- AC-4: Agent task plans decompose sanity checks, perf probes, capture comparison, bug triage, drawing inconsistency investigation, and pure-Simple optimization into independently assignable work packages.
- AC-5: Initial sanity and performance commands that can run on the current macOS host are executed or explicitly documented as blocked with the exact missing prerequisite.
- AC-6: Capture comparison evidence is produced when runnable locally, or a precise capture plan names the commands, expected outputs, and comparison criteria needed on the target host/QEMU setup.
- AC-7: No implementation change is marked complete until current evidence proves GUI correctness, drawing consistency, and performance against selected requirements and NFR targets.

## Scope Exclusions
- Release, version bump, tag, or push are out of scope until verification reaches PASS.
- Hardware-only validation outside the macOS host and local QEMU setup is out of scope unless the target is available in the current environment.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: code-quality).
- research: Added local/domain research, selectable feature/NFR options, agent task plan, system test plan, and initial evidence report.
- probe: Fixed missing Engine2D/IO compatibility modules blocking WM capture contract; host Metal smoke and render perf smoke pass; native Metal GPU readback, live QEMU capture, and full perf runner remain open evidence gaps.
- impl: Replaced the ARM64 dock letter placeholders with real procedural framebuffer icons and tightened the live QMP screendump assertion to detect icon artwork; Metal raw framebuffer readback proof, Engine2D Metal read_pixels GPU-download path, and pure Simple runner packed/i32 hot-loop optimizations are also in place. Capture and Metal readback evidence now pass; pure Simple C-parity NFR remains open.
- probe: Added `--full` CLI mode for the pure Simple runner; cranelift native-build is hash-correct but slower than `bin/simple run`, while LLVM native-build produces wrong hashes, tracked in `doc/08_tracking/bug/simple_runner_native_perf_hash_gap_2026-06-01.md`.
- probe: Added `test/perf/graphics_2d/fnv1a_native_repro.spl` and `--debug-pixels` runner diagnostics; LLVM matches the small FNV repro and representative pixels, so the remaining native mismatch is full-frame render/hash behavior rather than a trivial checksum arithmetic failure.
- probe: Extended runner diagnostics with row/window hashes and a 9x9 expected-pixel sample grid; LLVM native shows real sampled render mismatches, and conservative helper-return/single-pixel-loop experiments did not fix it.
- probe: Cleaned the minimal blit-tile repro and added a `[u64]` variant. Interpreter is correct in both; LLVM native at `--opt-level none` still corrupts later tile writes, so the bug is below benchmark logic and not caused only by `[i64]` pixel storage or LLVM optimization level.
