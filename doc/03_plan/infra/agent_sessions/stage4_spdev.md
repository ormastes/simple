# Lane: Stage 4 / `$sp_dev`

Goal: complete the pure-Simple x86_64 Stage 4 bootstrap, verify the exact fresh
CLI, and deploy it only after the bounded essential-tools smoke passes.

## Current state (2026-08-02)

- Stage 3 incremental refresh passes and normally reuses 724/727 cached units.
- Stage 4 reaches HIR lowering without the former `vulkan_backend.spl` parser
  ambiguity or phase-3 segmentation fault.
- The native `Dict.len() == -1` compatibility bug is handled by counting typed
  HIR dictionary keys.
- Fatal HIR errors stop before failed-module retention, preventing the former
  20-minute / 15.8-GiB post-HIR runaway.
- The latest bounded continuation fixed and pushed the cache-stat owner,
  shell/process owner family, and async random-access file owner through
  `180e4179c1a9`. Its three Stage 4 cycles advanced the HIR frontier from 395
  to 424 modules and proved each preceding blocker cleared.
- The invalid MIR convenience re-export is removed and Stage 3 was rebuilt
  from its admitted Stage 2 compiler: 724 compiled, 0 failed; identity,
  unsupported-command, frontend admission, and hash-stability gates passed at
  SHA-256 `adc4da69b802113f17980b88b783fe7ae6cfc1830ea93b6a660b51c68a2aba91`.
  The final Stage 4 cycle still reproduced the same three aliases at
  `target_family.spl` after 423 HIR declarations. This proves directory-package
  sibling registration is leaking each sibling's named imports into unrelated
  children; the compiler resolver itself is now the blocker.
- No fresh Stage 4 CLI has passed sanity or the essential-tools smoke, and no
  artifact has been deployed.

## Current continuation state (2026-08-03)

- The newest retained full-resource run used source revision `9e22a645a68`,
  admitted Stage 2 and Stage 3, loaded 2,116 sources, and completed all 1,431
  Phase-2 module surfaces.
- Stage 4 HIR reached module 427 of 1,431 and failed in
  `compiler.mir_opt.mir_opt.var_reassign_analysis`: its explicit facade import
  materialized `MirInstKind` without registering the payload types
  `GpuBarrierScope`, `GpuAtomicOpKind`, and `VhdlProcessKind` from the defining
  module's import context.
- Stage 4 HIR ran for approximately 26 minutes 34 seconds. The whole command
  used 43 minutes 23 seconds and peaked at 22,665,128 KiB RSS without swap or
  an OOM kill.
- Retained evidence is under
  `/tmp/simple-stage4-b1df.WmYLW6/build/bootstrap-stage4-b1df-cycle1/`:
  `stage4-bitcode-full.log`,
  `logs/x86_64-unknown-linux-gnu/stage4-native-build.log`,
  `progress-bitcode.log`, and `bootstrap-build-progress.events`.
- The initial dependency-closure candidate compiled the focused 135-module
  graph but its behavioral probe still exited 33 with `GpuBarrierScope`
  absent. It was not committed. Facade payload exports and consumer-local
  imports remain rejected workarounds.
- Current `origin/main` is `9299ca99288`. It includes cache-preserving
  unlimited one-binary mode, 16-module HIR progress, diagnostic-sweep
  preflight, and transient compiled-runtime string reclamation. These changes
  have not yet produced or qualified a Stage 4 candidate.

## Required next run

1. Fetch/rebase current `main` and preserve the existing Stage 3/native cache.
2. Fix the claimed explicit-enum payload dependency closure in the pure-Simple
   HIR/module-surface owner. Prove the exact facade route, an adjacent
   nested/aliased payload, and unrelated-symbol non-leak behavior.
3. Refresh Stage 3 incrementally because compiler sources changed.
4. Run one full-resource Stage 4 cycle with the progress/RSS watcher.
5. On a distinct failure, claim it in the bug DB, fix pure-Simple first, add
   exact and adjacent regression coverage, push, and retry within the
   three-cycle session cap.
6. On success, run sanity and
   `scripts/check/check-bootstrap-essential-tools-smoke.shs` against the exact
   fresh Stage 4 binary. Require test-runner, lint, duplicate-check, and
   aggregate PASS markers.
7. Deploy only that verified binary, record its path and hash, and update this
   document with the retained logs and evidence.

## 2026-08-03 enum-payload focused-probe continuation

- Three distinct setup probes are retained under
  `/tmp/simple-stage4-enum-closure3-20260803/build/mini_builds/`; none edited
  compiler source or wrote the canonical bootstrap cache.
- The same-package fixture was false green because sibling declarations masked
  the explicit-import closure. The cross-package fixture was false green in
  ordinary native-build mode. Adding `SIMPLE_BOOTSTRAP_STAGE4=1` did not reach
  HIR because the Stage 4 driver restricts entries to the CLI or OS main.
- Do not repeat those commands. The next scoped continuation must compile an
  executable in-memory HIR probe, or use only
  `SIMPLE_BOOTSTRAP=1`, `SIMPLE_STAGE4_STREAMING_SURFACES=1`, and
  `SIMPLE_NATIVE_ARENA_DECLS=1` without the Stage 4 entry guard.
- Merge-owner review found that the existing `if not already_bound` guard can
  prevent a declaration-only sibling binding from being upgraded by a later
  explicit enum import. The correct repair must combine an owner-safe recursive
  parser-type walk with a one-time materialization upgrade, exact alias/import
  resolution, conflict rejection, cycle protection, and unrelated-symbol
  non-leak behavior.
- This focused session reached its three-cycle cap. No Stage 3 or Stage 4 build
  was started, no source fix is claimed, and no deployment exists.

### Manual Stage 3 refresh invariant

Do not build `src/app/cli/main.spl` directly with a bootstrap-stage compiler and
call that result Stage 3. Stage 3 is the bootstrap compiler entry
`src/app/cli/bootstrap_main.spl`, built with `SIMPLE_NO_STUB_FALLBACK=1` and the
canonical runtime/provenance authority. A manual refresh is admitted only when
all of these checks pass:

- the build log contains no `Generating [1-9][0-9]* stub functions`,
  `FAILED FILES`, or `Build failed:` marker;
- `--version` prints exactly `simple-bootstrap 1.0.0-beta`;
- `run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl` exits 1 and reports
  `unknown command 'run'`;
- the canonical candidate frontend admission passes without changing the
  candidate hash.

`Build complete: ... 0 failed` and executable-file existence are insufficient
admission evidence. A stub-bearing full-CLI debug artifact can satisfy both,
yet silently fall through for `run`/`-c` and then produce an empty Stage 4 MIR.

## Exact fresh-candidate verification and deployment

The smoke accepts the candidate as its sole positional argument:

```bash
sh scripts/check/check-bootstrap-essential-tools-smoke.shs /absolute/path/to/stage4/simple
```

The bootstrap-equivalent form is
`SIMPLE_BINARY=/absolute/path/to/stage4/simple sh scripts/check/check-bootstrap-essential-tools-smoke.shs`.
Do not pass both forms with different paths. Require all four markers:
`essential_test_runner_smoke=true`, `essential_lint_smoke=true`,
`essential_duplicate_checker_smoke=true`, and
`bootstrap_essential_tools_smoke=true`. The script also rejects Rust-seed and
debug identities before running tool probes.

The canonical build/deploy command is
`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-cli --deploy`; it runs
candidate sanity, redeploy gate, essential-tools smoke, and provenance checks
before installation. Deployment copies the previous release binary to
`bin/release/<platform>/simple.pre_deploy`, installs the candidate, and restores
that backup automatically if the post-swap `-c 'print(1+1)'` smoke fails. On a
later manual rollback, restore that `.pre_deploy` file only if it still exists
and passes the same smoke; the successful deploy path intentionally deletes it.

## Performance evidence

- Stage 4 remains effectively single-core during frontend/HIR work.
- Recent fail-fast runs reach about 6.5--6.8 GiB RSS at 150 seconds.
- Whole-compiler cache identity can force 727/0 rebuilds; relaxing it remains
  unsafe until canonical complete MIR fingerprints and ordered direct
  dependency-interface hashes exist.
- Accepted optimizations remove redundant path canonicalization, deduplicate
  physical Phase-1 queue work, skip irrelevant facade-hint splits, and compact
  proven-unused retained implementation metadata.

## Post-x86 CPU/platform acceptance matrix

Run these only after the x86_64 Linux Stage 4 candidate passes its exact-binary
smoke. Merge owner is the primary Codex integration agent; final reviewer is a
normal/highest-capability Codex. Native bootstrap PASS requires the named host;
cross-object or QEMU rows are not substitutes unless explicitly stated.

| Acceptance ID | Platform / availability here | Canonical resume command | Prerequisites and retained artifacts |
|---|---|---|---|
| `ST4-PLAT-A64-LINUX` | AArch64 Linux; native host unavailable | `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --mode=dynload --full-bootstrap --full-cli --jobs=2` on AArch64 Linux | LLVM 18, C toolchain, Rust bootstrap prerequisites. Retain `build/bootstrap/stage3/aarch64-unknown-linux-gnu/simple`, `build/bootstrap/full/aarch64-unknown-linux-gnu/simple`, logs, hashes, and essential-tools markers. Current x86 Linux may run cross architecture gates, but not claim native bootstrap PASS. |
| `ST4-PLAT-MAC` | macOS x86_64/AArch64; host unavailable | `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --mode=dynload --full-bootstrap --full-cli --jobs=2` on macOS | Xcode CLI tools, Homebrew LLVM 18, coreutils and freetype. Retain matching `stage3/<triple>/simple`, `full/<triple>/simple`, logs, hashes, and smoke markers. |
| `ST4-PLAT-WIN` | Windows x86_64; host unavailable | `bash scripts/bootstrap/bootstrap-windows.sh --msvc --backend=llvm --mode=dynload --full-bootstrap --no-mcp --jobs=2` in Git Bash/MSYS2 | MSVC-compatible LLVM 18, Rust, Git Bash/MSYS2, `cygpath`; set linker flavor through the wrapper. Retain `build/bootstrap/stage3/x86_64-pc-windows-msvc/simple.exe` and logs. Full-CLI/deploy is currently restricted to Linux/macOS, so do not add it. |
| `ST4-PLAT-FREEBSD` | FreeBSD x86_64; safely runnable from this Linux host through QEMU | `sh scripts/check/check-freebsd-bootstrap-qemu.shs --full` | `qemu-system-x86_64`, qemu-utils, genisoimage, SSH key/client and rsync; provision the canonical FreeBSD 14.4 image plus trusted SHA-256 in shared media first. The wrapper is offline-only, then provisions guest LLVM/Rust dependencies. Retain `build/freebsd/bootstrap-logs/`, VM evidence, and guest `build/bootstrap/stage3/x86_64-unknown-freebsd/simple`. Never invoke the FreeBSD seed script directly on Linux. |
| `ST4-PLAT-SIMPLEOS-X64` | SimpleOS x86_64; safely host-driven from this Linux host | `sh scripts/bootstrap/bootstrap-from-scratch.sh --target=simpleos-x86_64 --output=build/bootstrap --jobs=2` | A verified host `bin/simple`, SimpleOS cross toolchain/QEMU prerequisites. Retain staged guest artifacts under `build/bootstrap` plus the emitted manifest/logs; this is a target lane, not a hosted full CLI. |
| `ST4-PLAT-SIMPLEOS-A64` | SimpleOS AArch64; safely buildable/QEMU-checkable from Linux after x86 acceptance | `sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` | Verified native compiler, LLVM backend, QEMU AArch64, frozen-source admission. Retain `build/os/fat32-arm64-desktop.img`, attestation manifest, logs, and follow with `check-simpleos-arm64-qmp-input-evidence.shs` when live input evidence is required. |
| `ST4-CPU-RISCV64` | Hosted RISC-V64 bootstrap host unavailable; cross/QEMU gates available here | `sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` | `riscv64-linux-gnu-gcc`, `qemu-riscv64`, RISC-V sysroot. Retain matrix evidence; this proves scoped cross execution/SIMD contracts, not a full hosted Stage 4 bootstrap. |
| `ST4-CPU-RISCV32` | Hosted target unsupported | Use the repository architecture gate for `riscv32-unknown-none-elf`; do not request `riscv32-unknown-linux-gnu` | RISC-V cross compiler/readelf. Retain ELF32/RISC-V attribute evidence. Bare-metal object acceptance only. |

Current host inventory (2026-08-02): Linux x86_64 with QEMU x86_64/AArch64/
RISC-V64 and AArch64/RISC-V64/MinGW cross compilers available. Therefore the
FreeBSD QEMU, SimpleOS host-driven, and scoped AArch64/RISC-V cross rows are safe
after x86 PASS; native Linux AArch64, macOS, Windows, and hosted RISC-V remain
external-host handoffs.

## Bounded continuation evidence (2026-08-03)

- Cycle 1 completed all 1,431 surface files and isolated the
  `parser_expr::parse_int_text` glob-facade ambiguity. Ownership was pushed as
  `e461e1a15d6`; the terminal-origin fix was pushed as `13c42480aca`. Exact,
  reverse-order, and true-ambiguity regressions passed 3/3.
- Cycle 2 cleared that boundary and reached LLVM code generation in 4:53.74
  (peak RSS 2,510,948 KiB). It found one failed file:
  `src/lib/nogc_async_mut/env/paths.spl`, where `variables` escaped HIR as an
  undeclared LLVM global. Ownership was pushed as `3f215e68979`; retained
  namespace-owner alignment and its synthetic 3/3 regression were pushed as
  `98354c3a0c5`.
- The current-main Stage 3 v10 refresh compiled 725/725 modules with zero
  failures in 127.6 seconds. Identity, unsupported-command rejection,
  compile/execute frontend admission, and stable hash passed at SHA-256
  `7edb495b6bda73f084081c4b3303cac3c1475ba040ff7084b7fa70aa5f48585a`.
- Cycle 3 reproduced the same real `variables` LLVM failure in 2:33.96 (peak
  RSS 2,610,832 KiB). Therefore the synthetic owner test is false-green for
  the real native entry-closure path and no Stage 4 binary exists. The bug was
  reopened and pushed as `33aaf57438e`; do not claim deployment or PASS.
- The same cycle emitted two nonfatal `platform_normalize` alias-owner
  warnings for the sync and async filesystem variants. They are separately
  tracked as P2/open in `83e45d29527`; they are not the fatal blocker.
- ARM and RISC-V work was paused for x86 priority. ARM stopped in Stage 1 with
  2,198 cached files and no Stage 2/3 binary. RISC-V retains an admitted Stage
  2 (`07a5b0d92995c8de4292c2295218d81b047a619716f41fa8c3d8edea61f29cc3`)
  and 323/725 partial Stage 3 objects, but no Stage 3 binary.

### 2026-08-03 fresh-session result

- The requested pure-Simple trace proved that `path`, `variables`, and
  `platform` namespaces are defined with retained owners; `env_get` resolves
  twice as a direct HIR call. No namespace global escapes into the preserved
  LLVM IR. The earlier `Option<SymbolId>` hypothesis is not supported by this
  evidence.
- Three diagnostic Stage 3 compilers rebuilt 725/725 while isolating the next
  boundary. Snapshotting `LlvmTargetTriple.to_text()` and reconstructing before
  calling the same method both remained false green under the Rust interpreter.
- Commit `a5f86301593` removes the retained target composite and composes the
  target triple inside `emit_module_header`. The compiled-native shard emits
  exact `x86_64-unknown-linux-gnu`; the `<invalid-heap:...>` target is fixed.
- `llc` now advances to generated IR line 2874 and rejects
  `%t281 = bitcast i1 %l162 to ptr` in `env.platform.detect_os`. The P1 owner,
  reproducer, and adjacent-test requirements are claimed in
  `llvm_bool_bitcast_to_ptr_invalid_ir_2026_08_03`.

The fresh session's three-cycle cap is exhausted. Do not rerun unchanged Stage
4. In the next scoped session, fix the claimed boolean-to-pointer lowering with
exact and adjacent pointer/integer tests, retry only the 1.4-second
`env/paths.spl` pure shard, refresh admitted Stage 3 once, then run one true
Stage 4 with `SIMPLE_BOOTSTRAP_STAGE4=1`. Keep LLVM fail-closed.

### 2026-08-03 x86 continuation result

- Pushed defined-SSA LLVM conversion hardening as `1a218e04c43` (focused 4/4
  PASS) without claiming it fixed the separate missing-store corruption.
- Pushed the staged-native SSA alloca transport repair as `cfef9087884`; named
  typed results retain definition/store flow in the focused native oracle.
- Pushed batched bootstrap authority hashing as `88bff46a6e2`: the complete
  43,191-file inventory fell from 181 seconds to 2.70 seconds without excluding
  vendor inputs.
- Rebuilt the bootstrap-only Rust authority, then admitted pure-Simple Stage 3.
  Sanity, capability, and provenance passed at SHA-256
  `aa0586ed281ae271b6254b8c21e3e0d847639dbdf644e7bef6c5ec07e1a43cf6`.
- True Stage 4 loaded 2,116/2,116 sources and completed all 1,431 Phase 2
  surfaces, then failed in the third HIR module. The only distinct diagnostic
  is `GlobalFlags.mem_infra_requested: [text]` being routed from Array into the
  Named arm. The focused retry retained its command/log/resource receipt and
  reproduced rc=1 in 2:52.22 at 829,044 KiB peak RSS.
- Three bounded candidates remained red after fresh pure-Simple compiler
  rebuilds: direct discriminant dispatch, typed prescan field rebind, and both
  combined. They are not merged. The session cap is reached; no Stage 4 CLI or
  deployment exists.

Next fresh session: instrument the exact parsed `ParserField.type_` immediately
before `lower_module` and at direct `lower_type` entry. Isolate parser storage,
field extraction, or method-call ABI before editing; reuse the exact Array plus
adjacent bool/custom/generic hard-exit regression. Do not retry the three
disproved candidates.

### 2026-08-03 enum-closure and backend-evidence continuation

- The executable in-memory HIR probe now reproduces the real state transition:
  a package sibling registers facade declarations with enum materialization
  disabled, then an authored explicit facade import requests the body. The
  admitted pure-Simple Stage 3 compiler built 135 modules in 45.0 seconds at
  389,256 KiB peak RSS; the pre-fix probe exited 34 at the first missing
  `GpuBarrierScope` dependency.
- Three bounded implementation/probe cycles did not produce an acceptable
  compiler change. The first closure draft advanced to exit 35, then direct
  walker assertions isolated `parser_variant_named_dependencies` at exit 60.
  An owner-local raw-discriminant draft still exited 60. No compiler source or
  unverified regression was committed.
- Highest-capability read-only review confirmed that the probe is exact and the
  recursive type/alias closure is structurally sound, but rejected the draft:
  collision identity compared only defining modules rather than terminal
  `(module, item, kind)` identity, and direct origins used lookup aliases rather
  than the physical `ModuleSurface.module_name`. Coverage also still needs
  bounds/defaults, every retained `TypeKind` form, same-owner/different-item
  collision, and module-surface alias-key cases.
- Next fresh session must first define owner-local typed `VariantKind` payload
  extraction in `parser_types.spl`, then add those missing adjacent cases. It
  must canonicalize every origin to the physical surface owner and fail closed
  on full terminal-identity conflicts. Reuse retained logs under
  `/tmp/simple-stage4-enum-closure4-20260803/build/mini_builds/stage4-enum-hir-probe/`;
  do not rerun the three failed drafts unchanged.
- Backend evidence was expanded independently: `796e6db366f` validates wrong
  LLVM/Cranelift lineage, real LLVM text-to-bitcode-to-object identity,
  malformed/tampered IR rejection, x86_64/AArch64 target separation, and
  CUDA/Vulkan/Metal artifact receipts without promoting unavailable hardware.
  `64280515b3f` adds five Source-through-optimized-MIR boundary scenarios and a
  synchronized generated/manual integration document.
- That coverage exposed and fixed a checker defect in `b6d694abc7b`: POSIX
  shell function-global arguments in `layer_result` clobbered the producer's
  Metal unavailability reason. Exact Metal plus adjacent CUDA/Vulkan reason
  preservation and generated-source fail-closed checks pass. The canonical bug
  row `gpu_backend_layer_result_reason_clobber_2026_08_03` is fixed.

### 2026-08-03 typed VariantKind continuation

- Read-only parser audit found that the retained probe's original unlabeled
  payload syntax was invalid for the flat enum bridge: `Variant(Type)` records
  no payload, while `Variant(value: Type)` records the expected tuple payload.
  This fully explains the earlier walker exit 60 and replaces the prior theory
  that raw VariantKind payload extraction alone was losing valid source data.
- Cycle 1 corrected the labeled-payload sibling probe. The admitted pure-Simple
  Stage 3 compiler (`62132c47fe04cac8fd9ddfda6d2a57b77995071a9631648350824957ade3cf61`)
  compiled 135 modules with zero failures and the executable exited 30.
- Cycle 2 added a direct-AST executable matrix for all 13 retained `TypeKind`
  forms and all three `VariantKind` forms. Its incremental native build compiled
  six modules in 2.5 seconds with zero failures and exited 30. The companion
  SSpec test-only commit is retained as `d00f0e00d164511276b06b0709cc3e149c24068f`;
  it is not merged until the helper implementation and a usable test runner are
  present together.
- Cycle 3 compiled the exact explicit-facade plus declaration-only-prebind HIR
  gate (135/135, 45.65 seconds, 397,288 KiB peak RSS), then crashed at runtime
  with signal 11/exit 139 after 1.16 seconds. GDB isolated the crash to
  `HirLowering.claim_materialized_payload_binding`, called by
  `register_imported_symbol`; the candidate used the fragile optional aggregate
  path `symbols.get_symbol(existing_id)`.
- The bounded cycle is exhausted and no implementation was committed. The next
  fresh continuation must replace that lookup with the established raw-ID path
  `existing_id.unwrap().id` plus `get_symbol_raw(raw)`, then rerun only the exact
  retained gate. Candidate source, exact/adjacent probes, and artifacts remain
  in `/tmp/simple-stage4-enum-closure5-20260803`; do not discard or repeat the
  two already-green setup gates.

### 2026-08-03 enum payload closure implementation

- The retained candidate's three-cycle continuation converged. The final
  runtime cycle used the admitted pure Stage 3 compiler at SHA-256
  `62132c47fe04cac8fd9ddfda6d2a57b77995071a9631648350824957ade3cf61`,
  compiled 4 modules with 131 cached and 0 failed, and the exact HIR probe
  returned its expected hard-exit code 30. Build wall/RSS were 20.17 seconds
  and 172,288 KiB; probe wall/RSS were 0.01 seconds and 4,352 KiB.
- `b400305d712` adds the exhaustive direct-AST parser dependency matrix;
  `f485c7dfe3e` adds typed `VariantKind` extraction and recursive explicit-enum
  dependency materialization. Both are pushed to `origin/main`.
- Independent review blockers were folded in: type-alias registration is
  first-write guarded, closure identity maps reset per lowered module, existing
  non-type bindings fail closed, and pre/post unrelated-import assertions are
  explicit. These last static audit amendments were not runtime-rerun because
  the mandatory three-cycle cap was reached.
- A fresh canonical x86 incremental-unlimited Stage 3/Stage 4 run is now the
  remaining full-graph proof. Do not repeat the focused gate in this session.

## Ownership

The parallel lane split, merge owner, and final reviewer are recorded in
`doc/03_plan/agent_tasks/stage4_spdev.md`.

## Post-Stage-4 future architecture

After the current exact x86 Stage 4 binary is admitted, continue with
`doc/03_plan/design/bootstrap_sdk_capsule.md`: a Clang-style, provenance-bound
frozen SDK -> candidate compiler -> rebuilt SDK/compiler -> reproducibility ->
atomic promotion flow. This future lane must complete the typed SHB authority
first; it must not narrow or replace the current full-source Stage 4 proof.

## Post-bootstrap SSpec gate

Once the exact x86 Stage 4 candidate exists, it runs
`test/03_system/check/post_bootstrap_stage4_acceptance_spec.spl` with adjacent
provenance. The gate rejects missing/symlinked inputs and verifies unchanged
retained smoke before deployment/rollback and platform acceptance.
