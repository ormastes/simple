# Bootstrap SDK Capsule Plan

Status: future design; execution is gated on an exact x86_64 Stage 4 candidate
that has passed `scripts/check/check-bootstrap-essential-tools-smoke.shs`.

## Purpose and non-goals

This plan makes the bootstrap SDK reproducible and cheap to consume without
making a capsule a substitute for the full-source Stage 4 proof.  It is the
post-admission design referenced by `.spipe/stage4_sdk_capsule_bootstrap/state.md`
AC-9.  Until AC-7 is recorded for one exact candidate hash, this document is a
reviewed contract only: no capsule, target row, deployment, or release changes
state to `pass`.

The SDK is an optimization for consumers that explicitly opt in.  A normal
bootstrap continues to parse and build the complete selected source closure.
The Rust seed is bootstrap-only and is never an SDK producer or consumer.

## Authority and ownership

`SHB` means the Simple Header Binary interface artifact.  It is authoritative
only for declared module interfaces, never for executable bodies.  The module
source remains the authority for a body and for every interface fingerprint.

| Owner | Authority | Must reject |
|---|---|---|
| Stage 3 provenance facade | parent compiler, source snapshot, producer and lock identity | changed source, a stale parent, symlink escape |
| Stage 4 provenance helper | exact full-CLI path/hash and build/smoke receipts | wrapper, seed, debug, stale, or alternate-output binary |
| SHB producer | normalized public interface and direct import fingerprints | body-only cache presented as an interface |
| capsule admission | complete manifest plus every content hash | partial, duplicate, foreign-target, or unbound entries |
| opt-in driver | a locally revalidated admitted capsule | implicit cache use or fallback after a capsule mismatch |
| promotion owner | generation directory and atomic active-pointer switch | in-place mutation of an admitted generation |

The implementation keeps these frozen interfaces exactly named:

| Interface | Required fields and invariants |
|---|---|
| `BootstrapSdkManifest` | schema version, target, backend, runtime bundle, compiler and Stage 4 provenance hashes, source revision, interface-set hash, body-set hash, generation, ordered module list, and whole-capsule hash |
| `BootstrapSdkModuleInterface` | canonical module id, direct imports, exported declaration signatures, interface hash, source hash, SHB path/hash, and schema version |
| `BootstrapSdkBodyArchive` | canonical module id, target/backend/runtime-bundle identity, body hash, archive path/hash, required interface hash, and producer hash |
| `BootstrapSdkProvenance` | absolute candidate path/hash, target/backend/runtime-bundle identity, Stage 3 manifest hash, Stage 4 provenance hash, producer/helper hashes, build/smoke log hashes, creation time, and rollback generation |

All paths in a manifest are capsule-relative, normalized, and must resolve
beneath the generation directory.  The only external paths are provenance
receipt paths, recorded as absolute canonical paths and hashes.  No manifest
may accept duplicate module ids, duplicate archive ownership, unpinned imports,
or an unrecognized schema field that affects admission.

## Deterministic capsule admission

The producer starts only after
`stage4_verify_candidate_provenance <candidate>.provenance.env <candidate> <repo>`
and the essential-tool receipt are both successful.  It uses the canonical
helpers rather than reimplementing identity checks:

- `scripts/check/lib/bootstrap-stage3-provenance.shs`
- `scripts/check/lib/stage4-candidate-provenance.shs`
- `scripts/check/check-bootstrap-essential-tools-smoke.shs`
- `scripts/check/build-core-c-bootstrap-runtime-capsule.shs` for the existing
  runtime capsule boundary, not as a replacement for a full SDK capsule.

Admission is deterministic:

1. Canonicalize the repository, candidate, Stage 3 manifest, and the selected
   target.  Require the Stage 4 candidate provenance to bind its source
   revision and exact essential-tools log.
2. Enumerate the module closure in byte-sorted canonical module-id order.
   Hash source content and normalized interface data; do not use mtimes as
   validity evidence.
3. Write one `BootstrapSdkModuleInterface` per module, then verify every SHB
   hash, direct-import interface hash, and the sorted interface-set hash.
4. Emit body archives only for the same target/backend/runtime bundle and bind
   each archive to its required interface hash and the exact producer hash.
5. Write `BootstrapSdkManifest` and `BootstrapSdkProvenance` last, re-read
   them, recompute all listed hashes, and reject any extra unlisted artifact.

External Stage4 SFFI providers follow the same immutable-input rule before the
link starts. Admission copies each validated archive/shared library, symbol
contract, provider receipt, and producer receipt into a private generation
under the Stage4 output root. The linker consumes only those copied artifacts,
never the caller's mutable paths. The logged Stage4 build command names the
provider-set receipt and its hash; candidate provenance replays that exact
receipt and verifies every copied artifact again. Selecting or rewriting a
manifest after the link cannot bind providers to an already-built candidate.

Provider receipts carry target, backend, runtime bundle, ABI, artifact format,
source revision, producer identity, and strong-symbol ownership. Admission
rejects symlinks, raw object formats regardless of filename, core-runtime or
compiler-backfill identities, duplicate ids/paths/content/strong symbols, stale
hashes, and foreign lane identities. Provider lists use receipt records rather
than colon-delimited paths so Windows drive letters remain unambiguous.

Provider validation cannot trust tools or symbol namespaces selected by the
provider being validated. The bootstrap lane supplies a separately admitted
LLVM 23.1 toolset receipt and expected receipt hash; that authority fixes the
canonical `llvm-ar`, `llvm-nm`, and `llvm-readobj` paths/hashes/version used for
archive inspection. Provider receipts may record that toolset identity but may
not choose or override it. Likewise, the Stage4 lane owns the allowed provider
ids and symbol-prefix contracts; a provider cannot authorize arbitrary `rt_*`
or compiler/runtime ownership merely by listing those symbols itself.

The canonical toolset-copy interface is
`llvm_23_1_snapshot_create ORIGIN_PREFIX ORIGIN_MANIFEST EXPECTED_MANIFEST_SHA256 SNAPSHOT_DIR`
from `scripts/check/lib/llvm-23-1-provider-snapshot.shs`. The expected digest
is selected by the bootstrap lane, never derived from a provider-selected
receipt. Consumers execute only tools below the returned
`LLVM_23_1_SNAPSHOT_PREFIX`; the copied origin receipt and rewritten snapshot
receipt are read-only generation inputs.

Snapshot replay compares every stable origin field with the sealed snapshot:
provider/lane/ABI identity, source revision, artifact kind/format, symbol
contract, producer identity, and LLVM toolset receipt. It then compares every
origin-declared content hash with the private copied file. Merely proving that
an unrelated origin receipt is well formed and hash-addressed is insufficient.
Archive admission inspects every member as a relocatable object for the exact
target format, architecture, bitness, endianness, and ABI; hostile/duplicate
member names and mixed-target archives fail closed.

A source change invalidates its interface and body.  An interface-hash change
also invalidates every reverse-dependent interface/body archive.  A body-only
change may retain dependent SHBs, but it invalidates that module's body archive.
Changing candidate hash, Stage 3 provenance, target, backend, runtime bundle,
schema, or producer/helper hash invalidates the entire generation.  Mtime is
only a fast *negative* probe; a hit always finishes with content-hash checks.

## Driver consumption and fail-closed behavior

Consumption is explicit, for example an eventual `--bootstrap-sdk=<path>`
driver option or an explicitly documented environment setting.  The default
driver path neither searches for nor silently prefers a capsule.  Before using
one entry it validates the complete manifest/provenance chain, its own target,
backend, runtime bundle, candidate identity, source revision, interface hash,
and archive hash.  On any mismatch it reports the rejected field and fails the
opt-in invocation.  It never falls back to a stale capsule, raw source, or the
Rust seed while claiming capsule success; an operator must rerun without the
opt-in or rebuild the capsule.

Bodies stay lazy: interface records are sufficient for import resolution;
archive material loads only for a reachable code-generation body.  This keeps
the existing SHB interface-cache idea separate from native archive ownership.

## Two-generation atomic promotion and rollback

Generations live under `build/bootstrap-sdk/<target>/generations/<id>/` and are
immutable after admission.  `active.sdn` is a tiny generation-id pointer and
is changed by writing, validating, syncing where supported, and renaming a
same-directory temporary file.  Readers open and validate the pointer once,
then use only that generation; they never traverse a mutable `current/` tree.

Promotion retains the new admitted generation and its immediate predecessor.
It creates generation `N+1` off to the side, validates every receipt, then
atomically moves `active.sdn` from `N` to `N+1`.  A failed write, hash check, or
driver smoke leaves `active.sdn` at `N`; partial directories are quarantined
and never selectable.  Rollback is the same verified pointer transition back
to retained generation `N`.  Retention pruning runs only after a successful
promotion and cannot remove either active or rollback generation.

## Performance inventory and evidence

Each admitted generation records cold and warm timings, peak RSS, module count,
SHB bytes, archive bytes, hit/miss counts, invalidation reason counts, and
candidate/source/interface-set hashes.  Compare equivalent source closures:

| Measurement | Required comparison |
|---|---|
| cold creation | full source closure versus first capsule build |
| warm import | source-interface resolution versus validated SHB resolution |
| reachable body load | source/lowering versus matching archive load |
| invalidation | body-only, interface, imported interface, deleted module, candidate, and target/backend changes |
| failure safety | interrupted generation, tampered SHB/archive, stale pointer, and rollback |

No timing result may claim an improvement if it changes source closure,
candidate, target, backend, or runtime bundle.  Debug diagnostics are useful
for profile/RSS capture but are not admission evidence by themselves.

## Test and documentation work after x86 admission

Add focused unit/integration coverage for deterministic ordering, hash and
path rejection, all invalidation cases, foreign target/backend rejection,
two-generation promotion/rollback, and opt-in fail-closed behavior.  Add an
SSpec using the frozen helpers named in state:

```
step("Prepare the incremental Stage 3 compiler")
step("Build the full-resource Stage 4 x86 candidate")
step("Admit the exact Stage 4 CLI and essential tools")
step("Package the reproducible bootstrap SDK capsule")
step("Preserve the post-x86 platform evidence matrix")
```

The planned setup/checker names are `setup_stage4_x86_candidate`,
`setup_bootstrap_sdk_capsule`, `check_stage4_exact_candidate`,
`check_bootstrap_sdk_capsule`, and `check_stage4_platform_matrix`.  Until
implemented, each fails with `fail("stage4 bootstrap helper is not implemented")`
or `assert(false)`; a passing placeholder is prohibited.  Generate an operator
manual under `doc/06_spec` only from a real executable spec and update the
matching guide/skill/agent contracts before verification.

## Post-x86 platform matrix

Every row is blocked until the x86 candidate and essential-tools smoke pass.
Each row produces a separate `BootstrapPlatformEvidenceRow` with target,
host/capability, exact command (or an explicit absent-command blocker),
candidate/capsule hashes, logs, status, reason, and resume command.  Cross/QEMU
evidence stays labeled as such.

| Row | Prerequisites and authoritative command | PASS boundary |
|---|---|---|
| Linux AArch64 | native AArch64 host; `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift --incremental-unlimited --full-cli` | native Stage 4 plus exact tools against its own hash; Linux cross objects do not qualify |
| macOS x86_64 | matching native macOS x86_64 host, Xcode/LLVM 23.1 provider; `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift --incremental-unlimited --full-cli` | native macOS x86_64 Stage 4 and smoke for its own hash; QEMU/cross is not a substitute |
| macOS AArch64 | matching native macOS AArch64 host, Xcode/LLVM 23.1 provider; `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift --incremental-unlimited --full-cli` | native macOS AArch64 Stage 4 and smoke for its own hash; QEMU/cross is not a substitute |
| FreeBSD x86_64 QEMU | QEMU image, SSH keys, `qemu-system-x86_64`; `sh scripts/check/check-freebsd-bootstrap-qemu.shs --full` | guest-produced and guest-checked evidence retained by the wrapper |
| SimpleOS x86_64 QEMU | sysroot and guest image; `sh src/os/port/llvm/sysroot.shs`, then `bin/simple run src/os/port/bootstrap_cross.spl -- --target simpleos-x86_64 --build-dir build/os/bootstrap --sysroot build/os/sysroot --seed src/compiler_rust/target/bootstrap/simple --verbose`. **Blocked:** no canonical compiler-in-filesystem QEMU wrapper currently exists. Required artifact: `scripts/check/check-simpleos-compiler-filesystem-qemu.shs` with a documented x86_64 guest invocation and retained serial/image receipt. | required filesystem payloads, in-guest `/usr/bin/simple --version`, and guest hello compile/run |
| SimpleOS AArch64 QEMU | prepared AArch64 image/QEMU; `sh src/os/port/llvm/sysroot.shs`, then `bin/simple run src/os/port/bootstrap_cross.spl -- --target aarch64-simpleos --build-dir build/os/bootstrap --sysroot build/os/sysroot --seed src/compiler_rust/target/bootstrap/simple --verbose`. **Blocked:** the same required wrapper must expose an explicit AArch64 guest invocation, image path, and serial receipt before this row can run. | same compiler-in-filesystem evidence in the AArch64 guest; host build and fixed-command stubs fail |
| RISC-V Linux | native RISC-V Linux host and provider/toolchain; retain the row even if unavailable | native target evidence only; Linux x86 cross output is `unsupported`/`blocked`, never PASS |

The SimpleOS rows must prove all required paths: `/usr/bin/simple(.smf)`,
`/bin/simple(.smf)`, `/sys/apps/simple(.smf)`,
`/sys/apps/simple_compiler(.smf)`, `/sys/apps/simple_interpreter(.smf)`,
`/sys/apps/simple_loader(.smf)`, and `/SYS/SIMPLETOOL.SDN`.  They also retain
the in-guest transcript for version, compile, and execution.  A guest QEMU
result establishes its guest row only; it never promotes native macOS, Linux
AArch64, or RISC-V rows.

## Completion gates

This plan becomes implemented only when an admitted x86 capsule has the full
test/manual evidence above, all available platform rows are verified, and
unavailable rows remain explicitly `blocked` or `unsupported` with their exact
resume command and retained artifacts.  Before a release candidate, run normal
verification and the release-bound `bin/simple test test --whole
--mode=interpreter`; no SDK or platform result weakens those gates.

The final verifier must additionally inspect changed contracts in
`doc/07_guide`, `doc/06_spec`, `.codex/skills`, `.agents/skills`,
`.claude/skills`, `.claude/agents/spipe`, and `.gemini/commands`; an unchanged
path is recorded as `N/A`, not silently omitted.  It must run, once on the
settled change, `find doc/06_spec -name '*_spec.spl' | wc -l` and require `0`,
`sh scripts/audit/direct-env-runtime-guard.shs --working`, and
`sh scripts/audit/direct-env-runtime-guard.shs --staged`.  The generated
manual and every new executable spec are reviewed for real assertions and no
placeholder pass before any done mark.  AC-12's implementation/spec/manual
work remains pending until an exact x86 candidate admits capsule execution.
