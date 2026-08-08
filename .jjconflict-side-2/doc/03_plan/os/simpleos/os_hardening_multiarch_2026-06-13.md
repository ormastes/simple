# SimpleOS Multi-Arch Hardening Plan — 2026-06-13

Goal: harden SimpleOS (SSH server, web server, FS-based file execution) on
x86_64, riscv32/64, arm64 (aarch64); harden the Simple compiler in perf and
codegen alongside. Work runs through the SPipe dev process
(`.spipe/<feature>/state.md`), split into small model-rated tasks, executed by
parallel agents with disjoint file scopes, reviewed by a higher model after.

## Tracks (disjoint scopes)

| Track | Scope (exclusive) | Spipe feature |
|-------|-------------------|---------------|
| A sshd-harden | `src/os/apps/sshd/**`, `test/*/os/apps/sshd/**` | `sshd_harden` |
| B webserver-harden | `src/lib/nogc_sync_mut/http_server/**`, `src/os/http/**`, matching tests | `webserver_harden` |
| C fs-exec-multiarch | `src/os/x86_64_fs_loaded_*.spl`, `src/os/kernel/loader/**`, fs_exec contracts/specs | `fs_exec_multiarch` |
| D compiler-perf-codegen | `src/compiler/60.mir_opt/**`, codegen specs `test/01_unit/compiler/codegen/**` | `compiler_perf_codegen` |

## Task breakdown with model rating

Rating = smallest model tier that can complete the task reliably.
haiku = mechanical/pattern-following; sonnet = implementation w/ judgment;
opus+ = cross-cutting design or review.

### Track A — SSHD hardening (sonnet lead)
- A1 (haiku): inventory unchecked-length / unchecked-index parses in
  `ssh_packet.spl`, `ssh_kex*.spl`, `ssh_transport.spl`; emit findings list.
- A2 (sonnet): bounds/length-prefix validation on every wire parse found in A1;
  malformed-packet specs (truncated, oversized, zero-length) in
  `test/01_unit/os/apps/sshd/`.
- A3 (sonnet): auth hardening — constant-time MAC compare audit, max auth
  attempts, kex algorithm-negotiation downgrade rejection; specs.
- A4 (haiku): spec run + doc-coverage pass over changed files.

### Track B — Web server hardening (sonnet lead)
- B1 (haiku): inventory parser limits in `http_server/parser.spl` (header
  count/size, request-line length, chunked decoding).
- B2 (sonnet): enforce limits w/ 431/413/400 responses; path traversal
  rejection in static file routing; specs for each limit.
- B3 (sonnet): slowloris/timeout handling in `server.spl` (read deadline),
  spec via injected clock where live socket not testable.
- B4 (haiku): spec run + lint pass.

### Track C — FS-based file execution, x86_64 + riscv + arm64 (sonnet lead)
- C1 (haiku): map current fs_exec marker contracts per arch (x86_64 done;
  riscv64/32 + arm64 scenario coverage gaps) from `qemu_runner*.spl`.
- C2 (sonnet): fail-closed parity — resident-manifest fallback must be
  rejected on riscv/arm lanes exactly as x86_64
  (`has_resident_manifest_fallback` equivalent); shared contract module
  instead of per-arch copies.
- C3 (sonnet): loader hardening — `kernel/loader` SMF load path: size/offset
  bounds checks, reject truncated images; unit specs.
- C4 (haiku): contract spec run for all arch lanes (unit-level; QEMU live
  lanes only if host has images cached).

### Track D — Compiler perf + codegen hardening (sonnet lead)
- D1 (haiku): re-read `doc/03_plan/compiler/perf/*.md` +
  `doc/03_plan/compiler/optimization/*.md`; list top 3 bounded, unlanded wins.
- D2 (sonnet): land 1-2 bounded mir_opt/codegen wins (pure Simple only — never
  the Rust seed); before/after timing evidence.
- D3 (sonnet): cross-arch codegen specs — extend
  `test/01_unit/compiler/codegen/` with riscv/arm64-sensitive cases
  (cross-module ABI, baremetal module-val) mirroring existing x86 specs.
- D4 (haiku): `bin/simple check` on touched compiler files.

## Review (higher model)
Each track's diff reviewed by an opus-tier agent for: cover-up fixes
(forbidden), weakened assertions, scope creep, missed bounds checks. Findings
fixed before commit is considered final.

## Process rules
- Each track agent commits per sub-batch immediately (`jj commit -m`), scoped
  to its own paths; never touches another track's scope.
- Interpreter-mode spec verification only (compile modes false-green).
- Stage4 test runs export `SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`.
- No skip()/TODO→NOTE/weakened assertions; root-cause fixes only.
