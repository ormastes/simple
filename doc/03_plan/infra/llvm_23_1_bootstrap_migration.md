# LLVM 23.1 bootstrap migration plan

## State

Blocked by the unintegrated binding port and absent local LLVM 23.1 prefix,
not by a compiler fallback.  `aya-llvm-sys 231.0.0-rc2` is now a candidate
Rust C-API package (`links = "llvm-23"`, `LLVM_SYS_231_PREFIX`); it must be
reviewed and vendored with an Inkwell `llvm23-1` feature before it is treated
as the compiler binding authority.

LLVM source authority is one of the upstream `llvmorg-23.1.0-rc*` tags pinned
by commit and source archive hash.  The eventual selection must be recorded
beside the binding package version, because the 23.1 release candidate is not
interchangeable with a later 23.x revision.

Candidate probe evidence (Linux host, 2026-08-08): a standalone offline Cargo
crate compiled `aya-llvm-sys = 231.0.0-rc2` with `no-llvm-linking` and
`strict-versioning`.  This proves the package is consumable by the local Rust
toolchain only; it does **not** prove Inkwell compatibility or LLVM 23.1 link
correctness.

Provider/link update (2026-08-08): the isolated 23.1.0-rc2 cache now supplies
`clang`, `llvm-config`, `llvm-as`, `opt`, `llc`, `libLLVM`, and LLVM C headers.
With `LLVM_SYS_231_PREFIX=/tmp/simple-llvm23-full-install` and the cache library
path, the same `aya-llvm-sys 231` probe builds and runs under strict versioning.
This is host-provider evidence only; Inkwell and the Simple Rust backend remain
on LLVM 18 until separately ported.

## Acceptance matrix

| ID | Requirement | Evidence |
| --- | --- | --- |
| LLVM23-001 | pinned host LLVM 23.1 exists | all tool versions/hashes agree |
| LLVM23-002 | Rust seed binds LLVM 23.1 | clean `--features llvm` build, no LLVM-18 link |
| LLVM23-003 | one resolver identity | mixed prefix/version negative tests fail closed |
| LLVM23-004 | pure-Simple tool discovery uses 23.1 | clang/assembler/optimizer/llc probes pass |
| LLVM23-005 | x86 Stage 2–4 are self-hosted | candidate, provenance, essential smoke PASS |
| LLVM23-006 | platform rows remain visible | FreeBSD/SimpleOS current host; macOS ARM external host handoff |

## Ordered work

1. Evaluate and adopt `aya-llvm-sys 231.0.0-rc2`, or an equivalent reviewed
   `llvm-sys` 231 release, under the vendored/offline Cargo policy.
2. Port Inkwell to expose `llvm23-1` against that package; vendor it, update
   Cargo manifest/lock, and repair Rust API
   changes under the LLVM backend feature.
3. Build a pinned LLVM 23.1 host prefix outside this repository; port SimpleOS
   LLVM-20 patches as a reviewed 23.1 series.
4. Change platform discovery, pure-Simple discovery, CI, bootstrap self-tests,
   and portability checks to reject 18/20 for this lane.
5. Execute the reviewed Mailbox Stage-2 replay, then the preserved-cache Stage
   3/4 chain with debug diagnostics and the exact candidate smoke.

## Current resume command

After an installed `/opt/llvm-23.1` and a compatible 231 binding:

```sh
LLVM_VERSIONS=23 LLVM_SYS_231_PREFIX=/opt/llvm-23.1 \
sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --full-bootstrap \
  --full-cli --mode=one-binary --incremental-unlimited --diagnostics=debug
```

The command is intentionally blocked until its binding prerequisite is true.
