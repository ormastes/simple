<!-- codex-architecture -->
# Windows Bootstrap on Separate Hosts: Nonconflicting Execution Plan

**Date:** 2026-08-30  
**Status:** Proposed; this document does not claim Windows Phase 2/3 admission is complete

## 1. Outcome and scope

Produce and admit pure-Simple Windows compilers through Phase 2, Phase 3, and
the next-compiler verification step on dedicated Windows hosts. MSVC and MinGW
are separate lanes with immutable inputs, private mutable caches, and signed
receipts. Linux cross-builds remain diagnostic and may prepare source/provider
evidence, but they cannot admit a Windows compiler.

This plan schedules execution only. It does not redesign reverse-reference
registries, implement the P0-P5 performance plan, or change the macOS bootstrap
architecture in
`macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md`.

## 2. Audited current boundaries

- `scripts/bootstrap/bootstrap-windows.cmd` enters Git Bash/MSYS2 and delegates
  to `scripts/bootstrap/bootstrap-windows.sh`.
- `bootstrap-windows.sh` materializes Windows symlinks, selects GNU or MSVC ABI,
  then delegates to the canonical `bootstrap-from-scratch.sh` pipeline.
- `bootstrap-from-scratch.sh` owns Phase 2/3 caches, provider identities,
  receipts, locks, admission, resume, and rollback behavior.
- `.github/workflows/windows-build.yml` builds seed/native-all and a Stage 2
  artifact for MSVC and MinGW, but its LLVM continuation is advisory and it
  does not establish the Phase2 -> Phase3 -> next-compiler admission chain.
- `.github/workflows/windows-tests.yml` and
  `.github/workflows/directx-windows-validation.yml` are validation consumers,
  not bootstrap authorities.

The macOS plan and reverse-reference/performance work may change semantic cache
keys. Windows execution must consume only reviewed schema versions; it must not
edit those owners or share writable caches with them.

## 3. Host and artifact topology

```text
Windows MSVC host                     Windows MinGW/MSYS2 host
  source revision S                     source revision S
  provider receipt P-msvc                provider receipt P-gnu
  phase2/msvc/simple.exe                 phase2/gnu/simple.exe
       -> phase3/msvc/simple.exe              -> phase3/gnu/simple.exe
       -> next/msvc/simple.exe                -> next/gnu/simple.exe
  immutable receipt bundle             immutable receipt bundle
                    \                  /
                     independent reviewer
                      -> admitted manifest
```

No binary, object, native archive, or mutable native cache crosses ABI lanes.
Producer-neutral parse/HIR/query artifacts may transfer only after the
performance/reverse-reference owner publishes an explicit portable schema and
the receiving lane verifies its digest. Until then, transfer cache metadata as
evidence only and rebuild locally.

## 4. Immutable inputs and receipts

Before a lane starts, freeze:

- source commit/tree digest and dirty-tree rejection;
- target triple, ABI, CPU/features, backend, optimization, object format;
- seed/Phase 1 executable, native-all/provider archives, compiler backfill, and
  every runtime capsule by SHA-256;
- bootstrap script/helper bundle digest, command vector, environment allowlist,
  Rust/C/C++/linker/SDK versions, runner image, and symlink-materialization report;
- HIR/MIR/object/cache schema versions and entry-closure identity.

Each transition writes `WindowsBootstrapReceiptV1` before promotion. The
receipt includes parent producer digest, output digest, compiled/cached/failed,
wall/CPU/peak RSS, cache lane identity, PE headers/imports, test results, and
failure category. Artifacts are uploaded under content-addressed names and are
never overwritten.

## 5. Cache transfer and invalidation

Use private mutable lanes:

```text
build/bootstrap/windows/<source>/<abi>/
  cache/phase2/<producer>/<closure>/
  cache/phase3/<producer>/<closure>/
  cache/next/<producer>/<closure>/
  artifacts/<phase>/<sha256>/simple.exe
  receipts/<phase>/<sha256>/receipt.env
```

Transfer is a tar/manifest pair containing immutable entries and per-file
digests. Extraction occurs into a staging directory; verification precedes an
atomic rename. Reject on source projection, producer/provider, target/ABI,
backend, feature, SDK, schema, closure, or action-key mismatch. Unknown or
missing reverse-reference generations fail closed to a local conservative
rebuild and record the fallback reason. Never let two agents write one cache,
and never reuse an MSVC object in MinGW or either Windows object on macOS.

The reverse-reference optimization lane owns key semantics and invalidation
algorithms. This Windows lane owns only cache transport, admission receipts,
and target execution. A key-schema change invalidates Windows imported cache
manifests without changing Windows scripts in the same commit.

## 6. Nonconflicting ownership

| Owner | May change | Must not change |
|---|---|---|
| Windows orchestration | Windows workflow, Windows wrapper, Windows receipts, PE gates | reverse-reference registries, macOS scripts, compiler semantics |
| MSVC host agent | private MSVC cache/artifacts/receipts | MinGW cache, shared provider source |
| MinGW host agent | private MinGW cache/artifacts/receipts | MSVC cache, shared provider source |
| Reverse-reference/perf owner | common key/schema and causal invalidation tests | Windows admission state or mutable caches |
| macOS bootstrap owner | Darwin runners, Mach-O slices, universal packaging | Windows PE/provider lanes |
| Merge owner | ordered reviewed commits and receipt schema | implementation in sidecar-owned files during execution |

Cross-owner changes become separate PRs with immutable handoff commits. Windows
qualification pins those commits; it never follows a moving branch.

## 7. Execution sequence

### W0 — Host qualification

Run native PowerShell/Git Bash checks for architecture, filesystem semantics,
Developer Mode/symlink materialization, tool discovery, SDK, antivirus
exclusions, disk/RAM, clocks, and signing availability. Fail before cache use on
an ABI/tool mismatch.

### W1 — Phase 2

Run the canonical full-bootstrap trust-root command with no stub fallback and a
private Phase 2 cache. Verify `simple.exe --version`, PE machine/subsystem,
imports, absence of ELF/Mach-O inputs and flags, bootstrap contracts, one source
compile, and one intentional negative control.

### W2 — Phase 3

Use only admitted Phase 2 plus its exact provider receipt. Preserve a separate
Phase 3 cache. Require native startup, focused compiler test, source/provider
lineage, no Rust-seed artifact substitution, and a real test-result summary.

### W3 — Next-compiler verification

Use admitted Phase 3 to rebuild the same entry closure. Compare normalized
Phase 3/next compiler outputs, command/input manifests, diagnostics, and
provider lineage. A binary mismatch is evidence to investigate, not permission
to replace either artifact.

### W4 — Tools and sanity

With each admitted compiler, build full CLI, test runner, lint/fmt/doc tools,
MCP, and LSP in producer-bound caches. Run version/help, compile/run a minimal
program, one passing and one failing test, lint positive/negative, MCP startup +
one request, LSP startup + initialize, and representative file I/O/process/network
sanity supported by the host.

### W5 — Package, sign, promote

Inspect before signing, sign the already-tested digest, inspect after signing,
run the signed candidate on the matching native host, and publish immutable
artifacts plus receipts. Promotion updates a manifest pointer; it never rebuilds.

## 8. Acceptance gates

| Gate | Required result |
|---|---|
| Provenance | Clean pinned source; exact producer/provider/tool/script hashes; no mutable input during a phase. |
| Phase 2 | Native PE starts, compiles a file, passes focused bootstrap/provider tests and negative control. |
| Phase 3 | Produced by admitted Phase 2, starts natively, and passes the same contracts without seed substitution. |
| Next compiler | Produced by admitted Phase 3; normalized comparison and lineage receipt complete. |
| Cache | Private writer; verified transfer manifest; causal hit/miss reasons; wrong ABI/schema/provider rejected. |
| PE | `file`/`dumpbin` or `llvm-readobj` confirms architecture, subsystem, sections, imports, and no ELF/Mach-O input. |
| Link policy | MSVC receives MSVC flags/libraries; MinGW receives GNU-PE flags/libraries; neither receives ELF-only policy. |
| Tools/tests | CLI, test runner, lint/fmt/doc, MCP, and LSP build and execute focused sanity with real results. |
| Performance | Cold/warm wall, CPU, peak RSS, compiled/cached/failed, critical path; no unexplained warm regression. |
| Security | No stubs/fallback, signing identity recorded, signatures verified, secrets absent from receipts. |
| Rollback | Previous admitted manifest remains executable; failed candidate cannot replace it. |

## 9. Sidecars, merge, and review

Before sidecars start, the primary owner freezes names
`WindowsBootstrapReceiptV1`, `WindowsCacheTransferManifestV1`, and
`WindowsAdmissionManifestV1`, plus shared checker step names
`step("freeze inputs")`, `step("verify cache")`, `step("build phase")`,
`step("inspect PE")`, and `step("run sanity")`. Incomplete checks use
`fail("not implemented")`, never placeholder passes.

Recommended independent lanes:

- MSVC native Phase2/3/next execution and receipts;
- MinGW native Phase2/3/next execution and receipts;
- cache-transfer/corruption/ABI-negative fixtures;
- PE inspection, signing, and rollback fixtures;
- tools/MCP/LSP native sanity matrix.

**Merge owner:** Windows bootstrap integration owner.  
**Final reviewer:** independent normal/highest-capability reviewer who did not
implement a lane. Lower-model sidecars may collect logs and draft receipts, but
cannot approve broad exclusions, generated manuals, or done marks.

## 10. Rollback and failure handling

On failure, preserve objects, cache, command, stderr, and receipt under the
candidate digest; mark the candidate rejected and leave the admitted manifest
unchanged. Cache corruption quarantines only the owning lane. Provider/schema
drift invalidates imports and starts a clean private lane without deleting prior
evidence. Signing failure rejects promotion but does not invalidate unsigned
build/test evidence. Re-running a green gate is prohibited unless an input
digest changed.

## 11. References

- `scripts/bootstrap/bootstrap-windows.cmd`
- `scripts/bootstrap/bootstrap-windows.sh`
- `scripts/bootstrap/bootstrap-from-scratch.sh`
- `scripts/bootstrap/bootstrap-cache-policy.shs`
- `scripts/bootstrap/rollback-bootstrap-deploy.shs`
- `.github/workflows/windows-build.yml`
- `.github/workflows/windows-tests.yml`
- `doc/03_plan/compiler/macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md`
- `doc/03_plan/compiler/bootstrap/stage3_native_cache_incrementality_2026-08-07.md`
- `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`

