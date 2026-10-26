# Cache, per-file and Phase 3 evidence reconciliation — 2026-10-26

Status: INCOMPLETE. This is a read-only reconciliation of retained build evidence,
not a new passing bootstrap, SPipe run, host certification, or release admission.
The requested endpoint remains the full cache/per-file and Phase 3 plans.

## Current execution evidence

| Retained lane | Terminal result | Interpretation |
| --- | --- | --- |
| `C:/dev/wt-rel3-new/build/s3-wp` | rc=1; 3,104 MIR errors; no successful compiler link | Supersedes the cache index's historical “in progress / 0 MIR errors” observation. |
| `C:/dev/wt-enumid/build/lane-A-old-wp` | rc=1; 6,739 seconds; 3,109 MIR-error lines; 2,854 payload-mismatch lines | The old compiler also fails the whole-program lane. Counts are diagnostic lines, not distinct defects. A newly introduced compiler regression is not established. |
| `C:/dev/wt-enumid/build/lane-C-new-hc` | rc=0; 448 seconds; zero MIR-error lines | The 122-module HIR-children closure compiled. Its entry dereferences a deliberately nil HirParam: build success is not runtime sanity. |
| `C:/dev/wt-enumid/build/lane-D-new-mcl` | rc=1; 1,190 seconds; 33 MIR-error lines; zero payload-mismatch lines; 10 TypeParam lines | 512 modules attempted, 509 succeeded and 3 failed. Optional payload pattern dispatch, unresolved `then`, and generic substitution remain observable failure families. |

No live bootstrap process was found during this inspection. The two live
`simple.exe` processes were TRACE32 MCP/LSP servers running the Rust seed;
they are unrelated and were left untouched. Retained terminal receipts are
used instead of restarting prior green or unchanged failed builds.

## Compiler identity

The current old-stage2 SHA-256 is
`1df6bc21737ca88a22d7342002abddc5fd0125182cbfec7d14f662db79cd2f54`;
the current new-stage2 SHA-256 is
`acfedbebd1db457efc0f8d1b0b3020dfa20711157bc090334c1b523a6a228779`.
Both match their local stage2 provenance receipts. These are current file
identities; the legacy lane script does not seal the executable digest in its
result file, so exact historical invocation identity still needs admission
receipt/log correlation. Do not present the comparison as a controlled bisect.

## Current provider facts

GitHub was queried directly on 2026-10-26:

- PR #4696 (P-G7) merged at `5e68862eed2a36a06c3f359dfbe455b8b71df054`.
- PR #4704 (release_phase3 integration) merged at `548babb59772b74bfd932d3ae5fa9f21bf9fa15d`.
- PR #4814 (worker argv) is merged.
- PR #4820 remains OPEN. Its body reports 8 cases, 6 passed and 2 failed;
  full specialization/native qualification is explicitly pending. It is not
  an admitted fix and must not be force-landed as if green.

## Remaining acceptance ledger

| Requirement group | Required authoritative evidence | Current verdict / next action |
| --- | --- | --- |
| Usable Phase 3 compiler | Authenticated closure objects, strict link, compiler builds/runs Hello World | Missing. Reduce the retained failure families before a changed-producer retry. |
| True per-file default | Self-rebuild with P-H, link/sanity, overlap receipt proving obj_done(A) < hir_start(B) | Missing. The local default-flip commit in wt-s3self2 is explicitly “never push”; do not publish it as qualified. |
| TLDR imported headers and AST sharing | File-open and parse counters, equivalent diagnostics/output, portable AST and target rejection | Not established by retained compiler-build receipts. Preserve every scenario in the active Phase 3 matrix. |
| SCV generations and invalidation | Changed/removed/new source and TLDR, forged digest/stale generation, negative query/config/aspect differential tests | Not established. Audit owning executable specs against the historical acceptance plan. |
| Async ownership and formal model | Single publisher, independent-key progress, cancellation/crash/SCC tests plus finite-model evidence | Not established. Do not replace concurrency evidence with helper tests. |
| IDE/SPipe tracking and recovery | Canonical delta parity, journal recovery, independent task progress and measured overhead | Not established. Requires real owner integration evidence. |
| <=100ms entry compilation | Admitted dependency preparation; p50/p95, CPU/RSS/opens/bytes/cache/lock evidence; one entry object | Missing. The 448-second closure build is not this benchmark. |
| Phase 4 products and host tests | Supported product builds/sanity, core/MCP smoke and appropriate runnable host suites | Missing. Six deferred native test products remain deferred, not passed. |
| SPipe evidence and landing | Real assertions, REQ traceability, generated manuals reviewed, verification PASS, reviewed merged PR | Pending. No overall PASS or completion claim. |

## Next implementation investigation

Inspect `hs_enum_payload` and `hs_pattern_payload` in
`src/compiler/40.mono/monomorphize/hir_subst/body_subst.spl`: retained failures
at lines 360/378 match bare Tuple/Struct against Optional payloads. Preserve
fresh and wrapped optional behavior; qualify the owner boundary with a tiny
native reproducer before changing it. Independently investigate unresolved
`then` and unsubstituted T in the 3 failed modules. Keep diagnostic stages
independent and retain cache identities; at most three fix/verify cycles per
feature. No unchanged full-bootstrap replay is justified by this report.

## Retained artifact hashes

These local paths are evidence locations, not portable repository assets.

| Artifact | SHA-256 |
| --- | --- |
| `C:\dev\wt-enumid\build\lane-A-old-wp\result.txt` | `d54fda7ab64548637e102734a1d2bc12d47a4e078e1386f2d985a3e26cfafe5f` |
| `C:\dev\wt-enumid\build\lane-A-old-wp\build.rc` | `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865` |
| `C:\dev\wt-enumid\build\lane-A-old-wp\build.log` | `7fd8bec09dde229d9b38833f46ece09653cd63d7f85919d43b6ddc91490bfc85` |
| `C:\dev\wt-enumid\build\lane-C-new-hc\result.txt` | `62ed66f7298a6c0570e058a3ff90297c514e531a82862ca106cba23667badd0c` |
| `C:\dev\wt-enumid\build\lane-C-new-hc\build.rc` | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |
| `C:\dev\wt-enumid\build\lane-C-new-hc\build.log` | `d66dee2d5b79a31fa72e4f2d96eeb2f47bb537667ee6473e0f567b41f71df945` |
| `C:\dev\wt-enumid\build\lane-D-new-mcl\result.txt` | `1185119adf0ff1ea2dc0d5c29ce7e32e25b9b063fcc3f98454110460555a4e14` |
| `C:\dev\wt-enumid\build\lane-D-new-mcl\build.rc` | `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865` |
| `C:\dev\wt-enumid\build\lane-D-new-mcl\build.log` | `1ee25aceb362d54c323c2e0a01695db9d280096101ab49ee1db7b0161a2daee8` |

## New reduced native probes — 2026-10-26

New probe sources are under
`C:/dev/wt-s2new/test/fixtures/compiler/optional_payload_owner_20261026/`;
outputs are isolated in `C:/dev/wt-s2new/build/optional-payload-owner-20261026/`.
Producer: the new stage2 executable identified above; target
`x86_64-pc-windows-gnu`, LLVM backend, `core-c-bootstrap`, admitted stage2
runtime authority, whole-program mode, one thread, frontend/HIR caches off,
120-second compiler timeout, and separate caches per probe. These are focused
Stage 2 diagnostics, not general SPipe execution or verification PASS.

1. `bare.spl` reproduces the ambiguous Tuple/Struct errors in a single module.
   Native build rc=1; mono reports no generics/unresolved specializations.
2. `qualified.spl` still fails, rc=1: payload owner differs from subject Option,
   Some is sought on the payload enum, and nil has no None variant there.
   Qualifying the four patterns in body_subst.spl alone is therefore insufficient.
3. `unwrapped.spl` tests explicit optional unwrapping before the payload match,
   covering implicit wrapping, explicit Some, and nil. MIR and native object
   emission succeeded (one module); aggregate rc=1 at link because CC was
   specified as `clang` rather than the required bootstrap-owned absolute path.
   This is object-generation evidence only; runtime behavior is unverified.

The first two cases reduce the retained failure independently of the 512-module
closure. Do not repeat them unchanged or rerun the full bootstrap to rediscover
these diagnostics.

### Link qualification boundary

The unwrapped probe emitted the retained 3,542-byte object
`aot-98039d51738f9352a70189f0a69d02d1a3cb44294f28be35d410f8aa87ff18a2.o`.
A focused manual strict-link attempt reused this object with the real owned
LLVM-MinGW clang and retained runtime archive. It failed with unresolved
`rt_strcat`, `WinMain`, and Win32 runtime dependencies. No native execution
occurred. Do not rerun successful MIR/object criteria: recover the canonical
startup/backfill and runtime link closure first, then retry only linking with
changed link inputs. No duplicate-definition forgiveness or stub startup was
used. The compiler source remains unchanged pending behavior qualification.

The focused diagnostic bug is recorded as
[optional payload owner dispatch](../../08_tracking/bug/native_optional_payload_owner_dispatch_2026-10-26.md).
The full plan remains active; generated manuals, SPipe execution, source repair,
full cache acceptance, Phase 3 linking, and PR landing are not complete.

| New probe artifact | SHA-256 |
| --- | --- |
| `C:\dev\wt-s2new\build\optional-payload-owner-20261026\bare.log` | `19b4cda6235000d52b8557de0fae75febe09638b8875dabb55fa874379666993` |
| `C:\dev\wt-s2new\build\optional-payload-owner-20261026\qualified.log` | `be20deeed70761f44903f00aaef091272c3dd14855f471a885276409e9be22da` |
| `C:\dev\wt-s2new\build\optional-payload-owner-20261026\unwrapped.log` | `094b30ddc2e6bfc6c057d45b61c5980dd716c0d9f52bf182a617d50b5ea40a13` |
| `C:\dev\wt-s2new\build\optional-payload-owner-20261026\manual-link.log` | `184ecde0e6ff29d921b656e3006d372c2950fdf67507855f4e05aaf592c92a94` |
| `C:\dev\wt-s2new\build\optional-payload-owner-20261026\aot-98039d51738f9352a70189f0a69d02d1a3cb44294f28be35d410f8aa87ff18a2.o` | `45d991e9fe57a9237316ae65559ca4e38656294fb6e3b3b7156dadacbcf2bab2` |

### Canonical archive pair follow-up

On the continuation turn the link inputs were corrected to the source-selected
backfill/native-all/backfill order and complete Windows clang support-library
set from `native_all_support.spl`, retaining compiler-rt/libunwind and strict
symbol checks. This link also exits 1: the admitted archives contain duplicate
Rust std/core definitions. The canonical argv is retained in
`C:/dev/wt-s2new/build/optional-payload-owner-20261026/canonical-link-args.json`;
errors are in `canonical-link.log`. No source compilation was repeated.
Runtime qualification remains incomplete. Do not add duplicate-symbol
forgiveness to turn this into admission. Recover a coherent runtime authority
or repair its assembly under the owning bootstrap contract.

Current release was fetched at continuation start: `194243b52bb`.
The clean existing `wt-bisect` worktree now owns branch
`work/cache-perfile-phase3-20261026`; no new worktree was created and no
unrelated main-worktree changes are included.

## Canonical linker correction and source repair — 2026-10-26

The preceding manual archive-only links omitted the canonical linker's fresh C
runtime objects, generated entry point and runtime-owner processing. Their
errors do **not** establish a production runtime archive defect. Source audit:
`llvm_native_link_orchestrator.spl` compiles C runtime objects unconditionally,
then generates the entry point and applies the runtime owner before linking.

A canonical native-build retry of the retained unwrapped probe with the owned
absolute CC path succeeded (rc=0) and its executable printed **`7 8 0`**,
covering implicit optional conversion, explicit Some and absence. Log/rc and
runtime output are retained under the original probe directory as
`owned-cc.log`, `owned-cc.rc`, `owned-cc-run.log`, `owned-cc-run.rc`.
The existing `cache-unwrapped` was retained; no cache-hit count is claimed
because successful parent output did not report one. This is a focused
Stage 2 native behavior result, not SPipe or full Phase 3 qualification.

The isolated release-based branch `work/phase3-optional-payload-20261026`
now changes the actual `hs_enum_payload` / `hs_pattern_payload` helpers to unwrap
before matching the distinct payload owners. The existing exhaustive match
and unhandled diagnostic remain. Added regression scenarios cover direct and
wrapped tuple/struct expression and pattern payloads, two substitution passes,
and absent payloads; their counting oracle also unwraps before reading payloads.

An actual-owner native diagnostic fixture imports the production substitution
functions. Its first launch was refused with SCV-E-ADMISSION for missing
first-checkout compile journal. The retry uses the documented cold-init flag
and the same cache, with the original refusal log preserved. No source
admission was bypassed. Build output is under
`C:/dev/wt-bisect/build/native_probe/phase3_optional_payload_subst/stage2-acfedbebd1db/`.
Qualification is pending; no changed-source test, manual, smoke, or merge is
claimed yet. General SPipe/docgen remains TEST_BLOCKED until an admitted
full pure-Simple runner is available; Stage 2 native diagnostics cannot replace it.

## Optional payload workaround native qualification

Workaround source commit: `9bebc55105d`; stable bug ID
`native_optional_payload_owner_dispatch_2026_10_26`; recovery base `b9f082ef085`.
Underlying optional-pattern/compiler compatibility work remains OPEN. Qualified
bug DB writer unavailable; dated canonical record retains pending reconciliation.

Both actual-owner fixtures import production substitution helpers rather than
copying the walk. The existing admitted Stage 2 was reused without rebuilding
Phase 2. Expression fixture: native build rc=0, run rc=0, output
`optional payload substitution: 5 cases, 2 passes each`. Pattern fixture:
requested jobs=80, native build rc=0, run rc=0, output
`optional pattern substitution: 5 cases, 2 passes each`. Each selected a
124-module closure. Counts cover direct/Some tuple/struct payloads, absence,
and a second substitution pass. Actual 80-way CPU utilization was not measured
and is not inferred from the requested job count. Do not rerun these green
criteria unchanged.

The SSpec additions, docgen/maintenance and compiler/lib/MCP full-CLI checks
are TEST_BLOCKED by the lack of an admitted general pure-Simple CLI runner.
These focused Stage 2 diagnostic results qualify this workaround's behavior,
not overall SPipe PASS, Phase 3 completion or a release. The next compilation
must contain the workaround to apply it; old immutable compiler bytes are
unchanged. The separate Future.then caller workaround remains under its
bounded native qualification cycle, not accepted as green.

| Qualified artifact | SHA-256 |
| --- | --- |
| `build\native_probe\phase3_optional_payload_subst\stage2-acfedbebd1db\build-coldinit.log` | `c3b79b60626850ce57ca885dc48d111103cad14423575beeb177b578be84a44b` |
| `build\native_probe\phase3_optional_payload_subst\stage2-acfedbebd1db\build-coldinit.rc` | `13bf7b3039c63bf5a50491fa3cfd8eb4e699d1ba1436315aef9cbe5711530354` |
| `build\native_probe\phase3_optional_payload_subst\stage2-acfedbebd1db\run.log` | `300d285460e328a1f7239db3ac8af6f2d7b812fafad55d22514ab225db1436cd` |
| `build\native_probe\phase3_optional_payload_subst\stage2-acfedbebd1db\run.rc` | `13bf7b3039c63bf5a50491fa3cfd8eb4e699d1ba1436315aef9cbe5711530354` |
| `build\native_probe\phase3_optional_payload_subst\stage2-acfedbebd1db\patterns-80.log` | `490e83292208680240e59d9cad5d6765a4c27abe878aac6d75da11d11dc85172` |
| `build\native_probe\phase3_optional_payload_subst\stage2-acfedbebd1db\patterns-80.rc` | `13bf7b3039c63bf5a50491fa3cfd8eb4e699d1ba1436315aef9cbe5711530354` |
| `build\native_probe\phase3_optional_payload_subst\stage2-acfedbebd1db\patterns-80-run.log` | `bcff6f9f76e88ea1529f3d69661873214c0bc1cfc20401a2b12b33bdeb2200f5` |
| `build\native_probe\phase3_optional_payload_subst\stage2-acfedbebd1db\patterns-80-run.rc` | `13bf7b3039c63bf5a50491fa3cfd8eb4e699d1ba1436315aef9cbe5711530354` |
