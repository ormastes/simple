# Windows Phase 2 runtime capsules

After writing a successful Stage 2 admission, `bootstrap-from-scratch.sh` invokes
`phase2-runtime-binding.shs publish` with that exact admitted compiler and runtime
authority. The SHA-addressed capsule lives under the bootstrap output's
`phase2-runtime-capsules/` directory. Its path and receipt hash are bound to the
compiler and admission hashes in `stage2-admitted/runtime-capsule.env`.
Publication checks the consumed runtime files against the admission's hashed
runtime snapshot, including the native archive, seed stamp, optional backfill,
hosted receipt, and hosted runtime. A self-consistent replacement archive and
stamp cannot acquire authority from an older admission. Retained capsules may be
reused only after these checks; binding writers are serialized.

Windows admission has a separate prerequisite: the bootstrap producer must bind
the path and version of LLVM 23.1.1 `clang-cl` in native C mode and reject LLVM
18.x, `cl.exe`, GCC, and C++ compiler fallbacks. The capsule pins that admission
and its tool-authority identity transitively; it does not duplicate compiler
selection or version parsing. Real Phase 2 acceptance therefore also requires
the producer's tool-authority receipt proving this prerequisite. A retained
older admission cannot satisfy the Windows bootstrap acceptance criterion.

The canonical writer emits only v2 capsule receipts and binds the required,
unique `artifact_layout` into the aggregate identity. The reader retains v1
compatibility for POSIX capsules only: v1 must omit `artifact_layout` and always
resolves the POSIX filenames. A v2 receipt must contain exactly one supported
`artifact_layout` (`posix` or `windows-msvc`). Missing, duplicate, unsupported,
or contradictory layout declarations fail closed in both the capsule verifier
and the phase consumer.

The v2 capsule receipt binds its platform layout into the aggregate identity.
MSVC capsules retain `simple.exe`, `simple_native_all.lib`,
`simple_compiler_backfill.lib` when present, and `simple.exe.inputs.sha256`.
POSIX capsules retain their existing names. Existing v1 POSIX capsules remain
verifiable. Mixed archive authorities, stale native/backfill stamps, changed
hosted runtime bytes, duplicate receipt keys, and overwrite attempts fail closed.

Git Bash's `chmod` cannot remove directory write permissions. On Windows,
`phase2-capsule-permissions.ps1` freezes and verifies an explicit Everyone deny
ACL on every capsule node. It denies content writes and namespace mutation,
including deletion of children. It rejects reparse points before traversing
them. As with POSIX permissions, the owner can deliberately thaw the capsule;
this is a write guard, not a security boundary against the owner. Receipt hashes
still detect content changes. POSIX verification retains its directory and file
mode checks.

`bootstrap-phase-verification.shs --phase=stage2` resolves the compiler's binding
before building tools. It validates the capsule and admission hashes, recomputes
the canonical source snapshot, and rejects a compiler admitted before the current
source changed. An explicit `--runtime-path` must equal that bound capsule.
Ambient `SIMPLE_RUNTIME_PATH` cannot select an unrelated runtime for Phase 2.

The source-owned regression is
`test/01_unit/scripts/phase2_runtime_capsule_contract_test.shs`. Run it with Git
Bash on Windows or POSIX `sh`. It uses inert compiler/archive fixtures and checks
real publication, permission denial, Windows filename preservation, stale
backfill rejection, successful admission binding, and stale source/compiler/
admission rejection. Its canonical invocation assertions cover the producer and
consumer wiring. A fixture PASS is not an admitted compiler or full Phase 2 suite
PASS; those require the bootstrap and phase test receipts from current source.

Publication occurs once per admitted compiler. The source snapshot check runs
once when Phase 2 verification starts. Neither operation belongs to a compiler
or language-server request path. No performance improvement is claimed.
