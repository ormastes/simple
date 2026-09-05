# Feature: simpleos-arm64-wm-qemu-fail-closed

## Raw Request

$sp_dev hardne simple os, on x86, arm, riscv. 1. harden simple web server, and simple db server on file system launch. 2. simple interpreter, compiler, loader porting to simple os and launch from file. 3. port llvm/clang and compile helloworl from fs. 4. list primary linux tools imple in simple and launchable through fs. 5. harden file system to support fat32, dbfs, nvfs, with shared interfaces. and run programs on the the fs. 6. harden simple sshd, simple web server to support all protocole it should support. 7. windows manager working check. go with pherallel and make a complete os. fix duplication and perf bug too.

## Task Type

bug

## Refined Goal

Make the ARM64 QEMU window-manager screendump scenario fail closed whenever its required build, QEMU, or evidence artifacts are unavailable.

## Acceptance Criteria

- AC-1: the ARM64 WM screendump scenario returns a failing verdict, not a diagnostic-only success, when its build step fails.
- AC-2: the scenario returns a failing verdict when QEMU or required captured artifacts are unavailable.
- AC-3: successful QEMU capture keeps the existing rendered-frame assertions unchanged.
- AC-4: one focused SPipe run records either a real pass or the exact unavailable prerequisite as a failure; no unavailable row is counted as PASS.
- AC-5: knowledge update is N/A for `doc/07_guide` and LLM expert skills because this only changes an existing executable test's failure policy; the existing ARM64 WM evidence plan remains authoritative. Any unresolved host prerequisite is retained in its existing plan/report rather than hidden as a skip.

## Scope Exclusions

No QEMU image build, compiler bootstrap, architecture-specific WM implementation, or evidence fabrication.

## Cooperative Review

N/A: this is a one-file fail-closed assertion correction. The already-completed high-effort campaign audit is the final reviewer for the surrounding evidence contract.

## Phase

dev-done

## Log

- dev: Created state file with 5 acceptance criteria (type: bug).
- impl: Build-unavailable and QEMU/artifact-unavailable branches now retain the blocker and call `fail(...)`; live capture assertions are unchanged.
- evidence: Focused interpreter scenario failed as intended with retained `arm64-wm-target-did-not-build`; the deployed command reported a bootstrap-seed warning. Changed-file lint crashed in that seed toolchain (exit 139) before a verdict and was not retried.
