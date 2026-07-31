# Shared Multilingual GPU Fonts — All-Items Verification

Date: 2026-07-28
Authority: selected requirements and NFRs in
`doc/02_requirements/{feature,nfr}/shared_multilingual_gpu_fonts.md`
Final done-mark owner: highest-capability `/root`

## Result

`STATUS: FAIL`

## 2026-07-30 restored-worktree execution status

The RV64 source repair was introduced at
`39c1863426a8c1379ee3c5584bb6c3d3a78f9970`. Stage2 attempt 29 is now
admitted at its exact clean launch checkpoint
`fbcaa8ccd0b22cc0169f5be289f7cc801d48b637`. The old temporary worktree and its ignored
Stage2/QEMU/spec/manual artifacts disappeared during the host Btrfs failure;
the tracked source, plans, historical identities, and pushed branch survived.
Filesystem allocation is usable again.

Physical Stage2 attempt 27 was stopped before Stage2 after preflight because an
unrelated full bootstrap and two Rust builds appeared. Attempt 28 then exited
before Stage2 because the restored worktree had no matching Rust seed/runtime
tuple. Both immutable logs are retained and neither path will be reused. The
attempt 29 used `--full-bootstrap --stop-after-stage2` only for the missing
Rust authority and exited zero after verified Stage2 in `37:34.35` at
`3,345,112 KiB` maximum RSS. Its binary SHA-256 is
`0b65b6109ddc0c4e8f924696a3e725a3d321f1fd094e5dfdaddaff7423a22fc0`;
provenance SHA-256 is
`55ecaabf0ba14ad5dbcf23b433cc7a5f6f97b153487b8a5fa0d83b5c05db39b7`.
The independent absolute-path manifest verifier exited zero. Scoped-tool
attempt 13 and its independent checker also passed; its evidence-manifest
SHA-256 is
`f2a5ead296c43c2b12354fb9eb754a70084f4813d985571bbeb7a544c93e0d84`.
The next serialized chain is reserved RV64 attempt 26, exact-ten attempt 13,
and manual attempt 13. No PASS is claimed.

RV64 attempt 26 exited 1 before codegen after the obsolete positional-entry
form selected broad unrelated HIR inputs. Attempt 27 corrected the canonical
source roots and explicit entry closure, then failed closed because admitted
Stage2 attempt 29 is Cranelift-only; this repository requires LLVM for RV64
freestanding targets. Attempt 26 took `0:28.19` at `658,208 KiB` maximum RSS;
attempt 27 took `0:43.22` at `85,024 KiB`. Neither produced an ELF. The next
minimal prerequisite is one LLVM-enabled current-checkpoint
`--stop-after-stage2` producer; Stage3/4 remain excluded.

That prerequisite is now admitted as Stage2 attempt 30 at source checkpoint
`fbcaa8ccd0b`: binary SHA-256
`c91c18017e9ffd4e5fcd0777f73c8563f1cd90ee096c26afca22d7f52a02d25a`,
provenance SHA-256
`3f270a6bad8b4102647c80c4fa65bf196d0ca8bcee8f43cab047dd5494474287`,
`backend=llvm-lib`, and `seed_features=--features llvm`. The producer and
independent manifest verifier exited zero in `39:40.05` at `3,553,108 KiB`
maximum RSS. The third and final bounded RV64 cycle is next.

RV64 attempt 28 consumed that final cycle and exited 1 in `1:36.46` at
`278,060 KiB` maximum RSS. The canonical explicit LLVM entry closure reached
`src/lib/gc_async_mut/gpu/browser_engine/dom_color.spl`, where LLVM method
resolution rejected suffix `.to_f32()` as ambiguous between `f64.to_f32` and
`i64.to_f32`. No ELF was produced. Command/stderr/time receipt SHA-256 values
are `4bc81f6c8dad6764c388cd32aed1aa294777f981854fd11c764e626de804674d`,
`d4d1505d429ecf5843dc28d56a49473b6afd92f03f23c1963f146e1bce584b80`,
and `6bc79ff953e370915e25973d708e8f98d64f4cd705d7e80ba72ab24448073ec2`.
The three-cycle cap is exhausted; QEMU, exact-ten, and manuals remain blocked.

`STATUS: FAIL`

## Historical 2026-07-30 Stage2/RV64 result — checkpoint 2a7e

Clean checkpoint `2a7e354c116` produced admitted Stage2 attempt 24: binary
SHA-256 `d8c2bee6ad33d58c7fa4aa8e1d8bc1b66fa9e887b920df7b79187757265ff79a`,
provenance SHA-256
`0bec61d68154e21d9cebb859578be6eb7cbe3dfc0fb6c03c3a222dafa682b83c`,
exit 0, `28:30.39`, and `2,438,756 KiB` maximum RSS. Its standalone manifest
verifier passed. Scoped-tool attempt 12 and its independent checker also
passed; evidence-manifest SHA-256 is
`cf7071a12808e862835feaf6a4e6b05b4d17138d3ed35cbb81b22c5f261b23d9`.

RV64 attempt 25 compiled the canonical full GUI runtime, but exited 1 in
`3:21.66` at `371,200 KiB`: the pre-GC unresolved surface contains 618 unique
symbols, including 597 raw hosted or unrelated runtime APIs; lld proves at
least twenty live failures before its error limit.
No safe attempt 26 exists until the closure/runtime owner is repaired. No ELF,
QEMU crop, exact-ten receipt, or manual receipt exists. See
`doc/08_tracking/bug/stage2_rv64_full_gui_runtime_closure_2026-07-30.md`.

The owner repair is now source-complete and focused-gate green: the RV64 entry
closure is 45 modules and excludes `vfs_init`, `vfs_boot_init`, `boot.cpu`, and
diagnostic logging; the focused Rust closure/selector test passes 2/2. This
does not promote status because the repaired source is not yet bound to a fresh
clean-checkpoint Stage2/tool admission and RV64 attempt 26 has not run.

`STATUS: FAIL`

## Historical Stage2/RV64 result — attempt 23

Canonical pure-Simple Stage2 attempt 23 is admitted at clean checkpoint
`94370c71ae81160cb4c3bd3c523092e5b12e855f`. Its binary is
`build/test-artifacts/shared_multilingual_gpu_fonts/stage2-bootstrap/attempt-23/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`
with SHA-256
`16bbd646fbb8281d2519db18112665759c8f2320b735cbf51f9071f8c6aa474f`;
its provenance SHA-256 is
`0fcdb0177678a5ac21e7595a3ee16f755a9e89b80dec90e54d3ec07c6d29594b`.
The producer and standalone manifest verifier exited zero. Elapsed time was
`35:06.28` and maximum RSS was `2,439,392 KiB`.

Scoped-tool attempt 11 is also admitted. The sealed evidence-manifest SHA-256
is `63a5cc1641fd680ea672f73bb8b4129d22d6cc1fe77f7f59d4f717eaaa0c516f`;
the independent canonical checker exited zero with
`stage2_font_scoped_tools_status=pass`.

RV64 attempt 23 used that Stage2 plus the explicit linker script. This cleared
the prior `_stack_top`, `_sbss`, `_ebss`, `spl_start`, `rt_string_data`,
`rt_string_len`, `rt_process_run`, and `rt_riscv64_syscall` failures. It then
exited 1 in `4:50.22` at `320,544 KiB` maximum RSS: the freestanding precheck
reported 724 unexpected symbols, deferred 717 candidates, and lld surfaced 20
live runtime symbols before its error limit. No ELF exists. Evidence is
retained at `/tmp/simple-font-rv64-attempt23-stage/evidence/`.

The attempt-23 blocker was coherent RV64 freestanding runtime ownership. Without
the ELF, no QEMU crop calibration, independent crop pin, exact-ten execution,
or canonical manual generation can run. Stage 3/4 and the umbrella
cross-platform native-GPU matrix remain deferred from this scoped delivery.

## Current active delivery scope — SimpleOS Stage 2 (supersedes)

The active delivery goal is `SIMPLEOS_STAGE2_FONT`. It covers exactly the ten
focused SimpleOS specs and their ten canonical manuals named in
`doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md`. The current manual
inventory is `0 missing / 9 stale / 1 source-current / 0 accepted receipts`.
The source-current pair is `selected_arabic_spec`; source currency alone is not
an accepted zero-stub docgen receipt.

Stage2 attempt 24 and scoped-tool attempt 12 historically satisfied the
compiler, runner/docgen, calibration, provenance, and independent receipt
gates at `2a7e354c116`; their ignored artifacts are no longer present and
cannot satisfy the current checkpoint. The
transactional 53-file staging, exact 59-source pin-set, Arabic/Hindi batch
identity, and native-safe fresh-device material changes remain downstream
behavioral claims until exact-ten runs. The owner repair is source-complete;
the next gate is current-checkpoint Stage2/tool admission. After that pair
links the canonical desktop ELF,
run and independently pin the QEMU crop, execute exact-ten attempt 13, then run
`bash scripts/check/build-stage2-font-scoped-tools.shs manuals-write
build/test-artifacts/shared_multilingual_gpu_fonts/stage2-scoped-tools/attempt-13
build/test-artifacts/shared_multilingual_gpu_fonts/simpleos-stage2-docgen/attempt-13`
and the corresponding independent `manuals-check`. Stage 3, Stage 4,
non-SimpleOS native GPU hosts, and the broader cross-platform matrix remain
deferred from this active delivery scope.

The current exact-ten command remains pending:

```bash
STAGE2_FONT_SPEC_ATTEMPT=13 \
SIMPLE_FONT_HOST_TOOL_DIR=<absolute-validated-mtools-directory> \
BUILD_DIR=build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live \
REPORT_PATH=build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live/report.md \
RV64_DISPLAY_SMOKE_ELF=build/os/simpleos_riscv64_display_smoke.elf \
RV64_WM_FONT_DISK=build/os/fat32-riscv64-desktop.img \
RV64_WM_FONT_REGION_EXPECTED_SHA256=<independently-reviewed-rv64-crop-sha256> \
bash scripts/check/run-stage2-font-scoped-specs.shs write \
  build/test-artifacts/shared_multilingual_gpu_fonts/stage2-scoped-tools/attempt-13
STAGE2_FONT_SPEC_ATTEMPT=13 \
bash scripts/check/run-stage2-font-scoped-specs.shs check \
  build/test-artifacts/shared_multilingual_gpu_fonts/stage2-scoped-tools/attempt-13
```

After those ten receipts pass, the exact manual commands are:

```bash
bash scripts/check/build-stage2-font-scoped-tools.shs manuals-write \
  build/test-artifacts/shared_multilingual_gpu_fonts/stage2-scoped-tools/attempt-13 \
  build/test-artifacts/shared_multilingual_gpu_fonts/simpleos-stage2-docgen/attempt-13
bash scripts/check/build-stage2-font-scoped-tools.shs manuals-check \
  build/test-artifacts/shared_multilingual_gpu_fonts/stage2-scoped-tools/attempt-13 \
  build/test-artifacts/shared_multilingual_gpu_fonts/simpleos-stage2-docgen/attempt-13
```

No scoped execution or manual has yet been accepted, so
`SIMPLEOS_STAGE2_FONT: BLOCKED`. The broader verification result remains
`STATUS: FAIL`. Historical Stage 2 and cross-platform records below remain
evidence history only.

## Current P0 admission status — 2026-07-29

`6a16b19cb5d` repaired aggregate dispatch: the current fixture now emits the
struct allocation and `%l2`. A new root cause was then localized to
`MirLowering.find_local`, which accessed instance state as `fn`; changing it to
`me` restores the receiver for every existing `self.find_local` call. The fixture
now observes `opt.?` through `print(owned.value)` and requires native output
`7`.

The latest bounded Stage 2 producer succeeded at
`build/native_probe/p0-admission-find-local-20260729/stage2-find-local-runtime-authority-core-simple`
with SHA-256
`f2db67c629f1fe1505e8374f1c4d701d23a5d1868820f58df02d115d475dc075`.
Its incremental receipt records 690 reused / 3 rebuilt, zero failed, and exit
`0`.

This remains diagnostic producer evidence because complete provenance and the
A/B/C admission receipts are absent, and no Stage 3 or Stage 4 CLI exists.
Accordingly every font evidence row remains unchanged: no native fixture,
essential tool, focused font spec, docgen manual, device, QEMU, or performance
row is accepted; `STATUS: FAIL` remains unchanged. Earlier producer failures
remain retained below as history.

## Historical diagnostic-only SimpleOS Stage 2 result — superseded

`SIMPLEOS_STAGE2_FONT: BLOCKED`

The historical scope was the ten-spec SimpleOS override in
`doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md`; Stage 3/4 and the
cross-platform GPU/performance matrix were deferred. Every PASS, accepted, or
green label in this subsection is diagnostic-only and does not advance a font
acceptance row.

- Runtime and runner gates: diagnostic-only PASS (non-acceptance). The
  pure-Simple Stage 2 compiler
  SHA-256 is
  `7f9f101472ba081ba89e58137820eb24fc8357f0d050c52c24fb725b6b14e142`.
  Reproducible Runtime6 archive SHA-256 is
  `a6d21c8fcf88d1ca788577a799564df022e917762abca1bad7736d3babb52782`;
  the repeated archive is identical. Its manifest SHA-256 is
  `6fd885abd620d180981f7a3f17be4328b2ded7dd802b41d4a347e222eff015a7`
  and reports `status=pass` and `repeated_build_equal=true`. The
  `rt_string_free` self-check output SHA-256 is
  `143283b26f5acc4162b35b2294b91df0943f8876294e773248f7b0c38fc5879e`;
  the coverage self-check receipt/output SHA-256 values are
  `a757b96d2692f285d0b4703e387129cb6945793896624bdc427c3a78ff7a4180`
  and
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
  The manifest records unique strong `T` providers in `runtime_native.o` for
  `rt_dir_list`, `rt_dir_remove`, `rt_file_copy`, `rt_file_hash_sha256`,
  `rt_file_rename`, and `rt_process_exists`. Runtime6 supersedes
  Runtime5/Runner5. Runner8 was accepted only for this diagnostic scope and
  supersedes Runner6 with binary SHA-256
  `8096d0897994d7602b23a8eadc6252ed1f7ea00bb811ebfc5a0f3050cf282440`
  and source SHA-256
  `093e013427a070f79889dc7dcb710063551533ae6cfc993e474d233f173a4c9e`.
  Its green receipt SHA-256
  `6afa15355dd3e1a4c05183b0a9d552c4757a01384b07d092b141510f54be05df`
  records 1 example / 0 failures / exit 0. Provider receipt SHA-256
  `b70fa412075a5a0a51593b68c02213ab9ce736115440f2259be0f8b9c2482466`
  records the runtime capsule at 7 examples / 0 failures / exit 0 and core
  I/O at 3 examples / 0 failures / exit 0. Historical Runner6 calibration
  receipt SHA-256
  `22bf1bf5850c333677621672b023b4106f7378a394545d730a7c24c4c22af93d`
  remains retained; its deliberate-red and zero-example contracts each
  passed exactly once.
- Manuals (diagnostic-only, non-acceptance): 10/10 commands exited zero and
  each reported
  `DONE Generated 1 docs (1 complete, 0 stubs)`. The immutable diagnostic tree
  is
  `build/test-artifacts/shared_multilingual_gpu_fonts/simpleos-stage2-docgen/attempt-1/`
  with SHA-256
  `a0af0d4e2d04625c2d493074b2b53f77be70b34851215e2ca70a9872f7ac7386`.
  Canonical promotion remains blocked with the executable specs.
- Assets: all three specs wrapped, then Stage 2 native-build exited 1 before
  examples. Supporting immutable asset/notice diagnostics passed 59/59, but no
  runtime PASS or acceptance is claimed.
- Shaping: all three specs wrapped, then native-build exited 1 before examples.
  Static source now includes registered-only Hindi, Arabic, and Urdu exact
  witnesses, handle-free Draw IR round-trip, and nonempty material checks; no
  runtime PASS is claimed.
- Material: the desktop production contract failed during native-build before
  examples. Source now rejects a valid zero-quad font batch and traces
  `SharedWmScene -> DrawIrComposition -> Engine2D -> FontRenderer`, but this is
  not runtime evidence.
- QEMU: the x86 wrapper contract reached 9/11 examples. Static reduction fixed
  three test-side placeholder interpolations and earlier stale source/input
  expectations, but the three-cycle cap forbids another run in this session.
  RV64 wrapped and then failed during native-build; no x86 or RV64 live guest
  proof was started.

One native-build blocker remains:

1. The third and final semantics-preserving parser probe advanced Stage 2
   discovery past the prior
   `src/lib/skia/feature/shaper/ot_layout_apply.spl:91:1` site and now stops at
   `src/lib/skia/feature/shaper/ot_layout_gpos_basic.spl:27`. The three-cycle
   cap is exhausted, so no fourth probe or speculative source edit is
   authorized.

Runner source now preserves native-build stderr and safely handles ordinary
multiline matchers while leaving manual/comment/raw-string content unchanged.
Runtime6 clears the prior six-symbol asset/RV64 link blocker, but supersedes
Runtime5/Runner5. Runner8 supersedes Runner6 and was diagnostically
source-matched, green, and provider-checked against Runtime6; the Runner6 and
older Runner4 calibration history remains retained. Focused execution remained
pending behind the capped parser blocker. Therefore 0/10 focused specs were
accepted and the scoped done mark remains absent.

## 2026-07-29 temporary Stage 2 and capped Stage 3 result

The temporary old-runtime-compatible Stage 2 producer is
`build/native_probe/memory-dispatch-fix/stage2-goal-rootfix2-simple`
(SHA-256
`0b1f741c9272a23c066ec42356949bfca7dca96605f8da4333fe0a8958b380ae`).
Its incremental receipt is 689 reused / 4 rebuilt, zero failed, 1m18.72s
wall time, and 304,068 KiB maximum RSS. It was not deployed and is not Stage 4
evidence.

The final allowed positional Stage 3 cycle passed physical-source parsing and
entered HIR, then exited 139 after declaring
`src/compiler/types/_TypeLayout/arch_and_verify.spl`. `/usr/bin/time` recorded
56.00s and 863,972 KiB maximum RSS. No output artifact exists. The retained log
is `build/native_probe/memory-dispatch-fix/stage3-goal-rootfix2.log`
(SHA-256
`456aa8bdd3b83e1ac6be0f092902491379c1d125ebf755af7091dcb84d260a79`).

That producer used the old runtime's mutating `Dict.set` form to pass the prior
nil-map crash. Independent P0/P1 review rejected shipping that compatibility
form because current main requires dictionary rebinding. The current six-file
source/test diff restores the rebinding, uses physical source keys at
entry-closure discovery, parse-cache insertion, and alias replay, keeps three
old-parent-compatible expression forms, and extends the existing dedup contract
test for those sites. Its source/test binary diff SHA-256 is
`aa209d0a2b51d523064f21529c32bcdeb17b2999d2d43a308dd55d06e0416901`;
it is build-unverified because the cap is exhausted. A fresh scoped producer
window may resume the exact failed command from
`/tmp/simple-font-sync-20260727`:

```bash
systemd-run --user --scope --quiet -p MemoryMax=16G -p MemorySwapMax=0 \
  /usr/bin/time -v -o build/native_probe/memory-dispatch-fix/stage3-goal-rootfix2.time \
  timeout -k 30s 1800s flock -n build/bootstrap/native_cache.lock \
  env -u SIMPLE_NATIVE_BUILD_RUST -u SIMPLE_BOOTSTRAP_STAGE4 RUST_LOG=error \
  SIMPLE_BOOTSTRAP=1 SIMPLE_COMPILER_PHASE_PROFILE=1 \
  SIMPLE_COMPILER_MEMORY_PROFILE=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NATIVE_RUNTIME_BUNDLE=all \
  SIMPLE_NATIVE_ARENA_DECLS=1 \
  SIMPLE_NATIVE_BUILD_TARGET=x86_64-unknown-linux-gnu \
  SIMPLE_NATIVE_BUILD_THREADS=1 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR=build/bootstrap/native_cache \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_RUNTIME_PATH=/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap \
  SIMPLE_BINARY=build/native_probe/memory-dispatch-fix/stage2-goal-rootfix2-simple \
  build/native_probe/memory-dispatch-fix/stage2-goal-rootfix2-simple native-build \
  --target x86_64-unknown-linux-gnu --backend cranelift --threads 1 \
  --cache-dir build/bootstrap/native_cache --mode one-binary --low-memory \
  --runtime-path /home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap \
  -o build/native_probe/memory-dispatch-fix/stage3-goal-rootfix2-simple \
  src/app/cli/bootstrap_main.spl \
  > build/native_probe/memory-dispatch-fix/stage3-goal-rootfix2.log 2>&1
```

This session must not rerun it: the three-cycle producer cap is exhausted.
Without a current Stage 3 and admitted full CLI, AC-3 and every dependent
runtime/docgen/native gate remain blocked.

`STATUS: FAIL`

## 2026-07-28 current-overlay incremental Stage 4 result

The SPipe skill and bootstrap rule now require Stage 4 to prefer a provenance-
bound incremental full-CLI build and accept a successful artifact directly;
there is no ceremonial clean replay. The exact current overlay, pure-Simple
parent, stable runtime, exclusive cache, two-thread command, and 32 GiB cap were
bound for three bounded cycles.

No Stage 4 CLI was produced. The profiled first cycle was stopped after proving
the old parent's per-expression instrumentation cost. The second cycle had no
compiler error but was selected by host `earlyoom` when unrelated jobs exhausted
RAM and swap. The resource-admitted third cycle completed HIR finalization, then
the cgroup OOM-killed `simple` at 33,483,972 KiB anonymous RSS before
codegen/link. Exact receipts are under
`build/native_probe/current-overlay-full-cli-fresh{1,2,3}/`; the tracked blocker
is `doc/08_tracking/bug/stage4_low_memory_rss_growth_2026-07-18.md`.

The three-cycle cap is exhausted. Essential-tools admission, calibration, the
48 focused commands, 44 font docgens, five compiler-prerequisite docgens,
native/QEMU/performance evidence, completion sync, and push remain blocked.

Source follow-up identifies and removes one high-confidence Stage 4-only
retention owner: unused legacy flat HIR and MIR accumulators duplicated the
canonical module graphs on the no-GC runtime. The gated path is unreachable to
Stage 4 consumers, and an independent ownership review found no P0/P1 defect.
The existing memory profiler now has a coarse
`SIMPLE_COMPILER_MEMORY_PROFILE=1` mode. Focused HIR diagnostics pass 4/4 and
both direct-runtime guards pass, but no new producer is permitted in this
window; the change remains runtime-unverified and does not promote any matrix
row.

`STATUS: FAIL`

## Historical 2026-07-28 host-independent completion audit

Parallel source audits fixed the remaining host-independent defects: GPOS
PairPos Device offsets now resolve from the owning subtable; the selected-font
SimpleOS skip is typed at the Engine2D rejection point; hosted compatibility
frames cannot claim Engine2D provenance; Engine3D retains one font-owner slot
and uses caller-owned plan/batch storage; and the four public font-renderer
surfaces export the out-parameter API. Independent code reviews found no
remaining P0/P1 in those paths. Exact host-independent Rust diagnostics also
pass: runtime UUID/LUID physical identity completed in 0.00s at 5,632 KiB max
RSS, and compiler wait/device-loss classification completed in 17.84s at
2,169,768 KiB max RSS. These diagnostics do not replace pure-Simple evidence.

Lane E now accepts only discrete/integrated devices with stable physical-device
identity, treats AA bounds as limits rather than observations, and writes each
attempt under its immutable attempt root. NFR-007 remains deliberately blocked:
the aggregate validates the focused native runner artifacts and owner-fault
trace directly, then fails closed with
`font-owner-device-loss-runtime-proof-unavailable` because the trace records
device-loss observed false and sequence zero. Owner-fault evidence cannot
promote the still-unproven device-loss recovery row.

The source-only reliability repair uses `i64` fault codes rather than aggregate
or enum transport on native hot paths. Atlas replacement is transactional;
unknown fence completion poisons the backend and retains potentially in-flight
resources; shutdown keeps an incomplete Engine3D owner; fallback counters move
only after a successful CPU commit. Reused plan/projection and vertex-byte
buffers remove the new per-draw scratch churn; the completed vertex pool is
bounded, deferred fallback retains one snapshot, and Engine2D clears fallback
pixels after use. Full-frame proof readbacks remain bounded P1 profiling work,
not an observed leak.

At that checkpoint, the final settled-overlay static gate passed for all 75
paths and 18 changed specs: diff/whitespace, canonical matcher and placeholder,
Stage3 cache-shape,
font allocation/lifetime, current-count, and working direct-runtime ownership
checks are green. The aggregate itself still exits 1 with the expected exact
runtime-proof blocker above.

The executable-manual inventory is 44 font specs (19 missing mirrors, 25
stale, zero current) plus five missing compiler-prerequisite mirrors. The
focused graph has 48 commands: preflight, B6, C19, D13, and E9. With no
admitted full CLI, no runtime, docgen, native, QEMU, or performance acceptance
row can run. The mechanical matrix remains `0 pass / 0 active / 24 blocked`.
The corrected twelve-criterion control matrix is `1 pass / 6 active / 5
blocked`: AC-2 passes; AC-1, AC-7, AC-9, AC-10, AC-11, and AC-12 are active;
AC-3–6 and AC-8 remain blocked. AC-9 stays active until every retained-path
contract is complete, and AC-10 stays active during the current parallel
integration. Source-lane activity does not promote a REQ/NFR row. The
75-changed/new-path checkout at tracked checkpoint `24a77be3c89a` and its
87-behind / 70-ahead relation to the then-recorded `origin/main` are historical.

The current clean feature branch is
`codex/shared-font-sync-20260727` at `97d91f1b476`; it matches the locally
recorded feature-branch remote (`0 ahead / 0 behind`). This checkpoint does not
complete AC-12: final verification, completion-time fetch/rebase, file-count
guard, and eligible push remain open.

`STATUS: FAIL`

This is the current all-lane audit, not a runtime or native PASS.
Compiler-enablement work is not a shared-font acceptance criterion and cannot
promote a font row. The branch nevertheless retains the minimal HirBlock,
lowering-error collector, native-arena, and direct-entry repairs needed to
produce the pure-Simple prerequisite.

### Current identity and synchronization source ownership

| Owner | Writable scope | Exact queued focused command | Retained root | Final reviewer |
|---|---|---|---|---|
| `font_native_perf_audit` | Simple-side stable physical-device identity propagation through existing Engine2D/Engine3D Vulkan owners and immutable native/perf evidence; performance-helper, backend-fault, metadata, and native source-contract specs; no Rust runtime identity/sync implementation | `run_focused_spec test/01_unit/helpers/shared_multilingual_gpu_fonts_perf_evidence_spec.spl`; `run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl`; `run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_device_metadata_spec.spl`; after runtime admission and real hardware, `run_focused_spec test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl` | `build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/` | `/root` |
| `font_surface_audit` | Engine2D scalar owner-fault receipt and scratch-reuse source contract | `run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_font_scalar_receipt_spec.spl` | `build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/` | `/root` |
| `font_matrix_audit` | hosted-WM live-proof focus/provenance source contract | `run_focused_spec test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl` | `build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/` | `/root` |
| `stage3_hir_lifetime` | runtime selected-device identity, fence-wait/wait-idle last-error retention, runtime symbol/codegen/interpreter and canonical Vulkan SFFI facades; no Engine2D/Engine3D evidence-record ownership | `run_focused_spec test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl` | `build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/` | `/root` |

These commands remain queued until a future admitted pure-Simple CLI/core-C
identity exists; the native readback command also requires one
discrete/integrated Vulkan device. No command is executable merely because its
source lane is active.

### Historical bootstrap blocker snapshot

This subsection preserves the earlier `24a77be3c89a` producer snapshot. Current
P0 authority is the 2026-07-29 admission status at the top of this report. At
the historical checkpoint, P0 was owned by `/root` for a future fresh producer
window only, with `/root` as final reviewer. That exhausted window could not
execute another producer or full bootstrap. Retained cache/profile inputs
remain under `build/native_probe/`,
notably `stage3-importfix-cache/`, `rebased-stage4-cycle3-final.log`, and
`lazy-sibling-stage3-cycle3-pure/build.log`. They are blocker/resume artifacts,
not runtime admission. The conditional resume and hash-bound admission command
below remains authoritative only after a future window first proves an
immutable pure-Simple parent/current-source receipt.

The historical producer input was the isolated overlay rooted at
`24a77be3c89a`, not the historical detached checkpoint. Its tracked
`src scripts test` binary-diff SHA-256 is
`c5233e73b817e1ca915aa768f62856200b7fc43b542b2715d03ed7c5eab218b1`;
the additional untracked source owner
`src/lib/common/gpu/font_owner_fault_receipt.spl` has SHA-256
`032978d4654af8011f0d0bd084119dc7ed035bf8710d03c6928318c56a33817b`.

The tracked implementation checkpoint under verification in that snapshot was
`24a77be3c89adb1f46a53cbcb53602a904305345`; current evidence working changes
then followed it without inventing a commit hash. The earlier pushed checkpoint
`2eb2bbf93f10` is historical. Completion still requires the final
fetch/rebase/file-count gate against the then-current `origin/main`.
At the earlier source checkpoint `deb90cd8a9c`, both direct-runtime guards,
both numbered-artifact guards, `git diff --check`, and the
zero-executable-specs-under-`doc/06_spec` layout gate passed. Those retained
static results do not prove the current checkout, runtime behavior, or a
native row.

Current source replaces the quadratic sibling resolver with one
shared package-sibling index and makes Stage3 use the pure positional route,
the native-all runtime bundle, and forwarded target/cache/thread/runtime
environment. Environment/profile decisions and their diagnostic construction
are hoisted once per compiler invocation rather than repeated per expression or
source. All three producer cycles are exhausted. The retained pre-fix
profile exited 124 after 30:04.76 with maximum RSS 21,850,164 KiB (log SHA-256
`090e9775f618052004b1f451b3709fc49add60823a12cec4318117827dfeead5`).
The later current-source producer also exited 124 after 30 minutes in HIR,
produced no child, and has log SHA-256
`b5b2aaa6d8b5eae73e863c7ae6c5fd3af29f675a6f3562d08c14e9a663c69bfe`;
its last sampled RSS was 19,841,980 KiB at 27:16. There is no fourth retry.
No admitted CLI/core-C identity or global runner calibration exists.

The external compiler workspace at stale source `c167e2509f4` ended Stage4
with `EXIT=143`/SIGTERM and produced no full output. Its retained log SHA-256 is
`5a49ab01a7f7db6fc112c77c605c4760ff1a68f6929e5cf1e7037deef8d1c1d7`.
The stale Stage3 artifact (`01ef253d...3c3c7`,
`full_cli_status=separate-not-proven`) is historical only. No eligible parent
or current admission route remains in this verification window.

One isolated clean-current attempt was made only because this admission is
essential. Rust seed
`/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple` ran
against clean HEAD `16ebfdb6410` in `/tmp/simple-clean-cli-20260726`, but was
terminated with SIGTERM after 2m15s before compilation/object output. No
candidate CLI emerged. Its final meaningful log line was the pre-compilation
memory guard warning that `SIMPLE_LIB=src` contains 600+ `.spl` files; retained
log: `/tmp/simple-clean-cli-20260726/build/mini_builds/full_cli_seed_cycle1.log`.
This is a separate compiler/runtime build-system blocker. The font lane must
not restart it; its owner must resolve that admission path and deliver one
full CLI before the queued verification can resume.

A final P0 admission lane in `/tmp/simple-pure-cli-font-20260727` at
`1d75d521b775` spent the three permitted incremental cycles with retained
pure-Simple Stage3 compiler SHA-256
`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`.
Cycle 3 stopped in
`src/std/nogc_sync_mut/compression/gzip/lz77.spl`: line 104 binds the reserved
keyword in `val match = ...`, and line 105 uses it in
`val distance = match[0]`. The retained parser reads that use as a `match`
expression and first reports `expected :, got Newline`; the line-106
`length` diagnostics are recovery cascades, and `length` is not reserved.
The retained and clean-current token tables are byte-identical at SHA-256
`cfea0c9e2063eae474913ee9cbfd585d29dfd50323c24c375d23656b884119da`,
and all three logs retain the same parse ordering, with cycle 3 reaching 801
of 1,309 unique physical sources. No candidate ELF and no native-cache
object/file were produced. The retained logs and SHA-256 values
are `build/mini_builds/full_cli_incremental_cycle1.log`
(`82a5b6bf68efc867e7e8cf4107ebe29f14590ec422e7646a87eac10f1fdad389`),
`full_cli_incremental_cycle2.log`
(`c1e4e61d1cf919478793017859c09cc021938863a651ab198e48f37759f1f8dd`),
and `full_cli_incremental_cycle3.log`
(`4bab47a3a0ff2164508db9ada5433cfbe85b8fdeb100756328b8869450e39dc7`).
The historical continuation at that checkpoint called for a canonicalized
closure preflight and an isolated compatibility bridge. That instruction is
superseded by the current fresh-Stage2 plan below. Only the genuine
current-language `class` local corrections in
`src/lib/skia/feature/shaper/ot_layout_gpos.spl:123,602` belong in the font
branch; the 13-file bridge overlay remains isolated, uncommitted, and
unmerged. The three-cycle cap is reached; this blocker does not promote any
runtime-dependent font row.

A fresh compatibility-bridge continuation then ran in detached worktree
`/tmp/simple-cli-bridge-20260727-2` at feature checkpoint `397afaaee3bb`.
The bridge remained isolated and uncommitted. Its three bounded cycles cleared
the reserved-keyword and multiline-boolean parser blockers and the first
`FileTreeState` HIR type gap, but still produced no ELF and zero cached object
files. Cycle 3 raised the per-file limit from 60 to 180 seconds and stopped on
two terminal blockers: the 9,716-line
`src/app/office/sheets/formula.spl` still exceeded 180 seconds, and
`src/lib/editor/70.backend/gui_backend.spl` reached the next missing direct
type resolution (`SettingsViewState.categories` is lowered as `ANY` in
`gui_render_settings_html`). The three retained log SHA-256 values are
`1a4c04ee995bb80ac55e3650e7088e773326f8b16bc25d9c8952d016b3886def`,
`43e9dff528a8ce0f33746be503368bcbd416c6eb22c85c43867bcc06d89adc7a`,
and `09e3e54a99ab7d76681ca2a27cd285b8ebb71932b27fed65a15ee133c0508c12`.
No essential-tools smoke ran because no candidate existed. The session cap was
reached; its former resume instruction is historical and superseded by the
current fresh-Stage2 plan.

The next isolated continuation used detached worktree
`/tmp/simple-cli-bridge-20260727-3` at `fefcfe011fc0053d0ab3e01a13005bb841db5023`
and the same retained Stage3 compiler. The bridge avoided eager Office/IDE
entry closure, added the proven GUI type imports, and selected the complete
Rust runtime archives. Cycle 1 retained 1,417 objects before a link-only
failure exposed the incomplete default runtime bundle and missing GSUB
`_sub_end`; cycle 2 cleared those blockers and stopped on one canonical CSS
import plus the duplicate `ant-trace`/`ant_trace` module; cycle 3 cleared the
full import/collision preflight and parsed 806 of 1,190 unique files before the
retained parser rejected `loop.induction_var` in
`auto_vectorize_analysis.spl`. Log SHA-256 prefixes are `b5db2444`,
`567d1e0d`, and `7732687e`. No ELF or smoke result exists. The genuine bounded
GSUB helper is integrated; all remaining compatibility edits stay isolated.
The three-cycle cap was reached. Its retained-cache resume instruction is
historical and superseded by the current fresh-Stage2 plan.

A later fresh three-cycle bridge window reused the same Stage3 SHA-256
`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`
and all 1,417 retained objects. Cycle 1 rejected `pub mod` at
`src/compiler/10.frontend/core/__init__.spl:111`; cycle 2 cleared that bridge
syntax and then rejected five address-of forms, first
`src/os/userlib/device.spl:26`; cycle 3 cleared those exact closure forms and
stopped at the sparse ABI enum discriminants beginning with
`src/os/kernel/types/syscall_types.spl:8`. The retained log SHA-256 values are
`641d8754567044305afeb9abe612bd86b1fbbcbafffc40d6f57a3c168ac34fce`,
`6559f179b3058111fc72718864d1dc9ee642cf401f93a1f684781b05aacdc48d`,
and `f8bb267073a05f345319d36c1622d5477751be45249ff0d6b1063f3664fc8a32`.
No ELF, Stage5, or essential-tools smoke exists. The bridge remains isolated;
the former sparse-ABI continuation is historical and superseded by the current
fresh-Stage2 plan.

Fresh admission lane `/tmp/simple-cli-admission-20260727-4` then preserved all
106 sparse ABI values through exhaustive enum-to-number converters and reused
the 1,417-object cache. Cycle 1 cleared three tuple-destructuring loops
(`build/mini_builds/full_cli_admission_cycle1.log`, SHA-256
`769acbbb1a10cc1cb825f1704a7e563118e42a3725290fcaff5a508fc6e4a7ae`);
cycles 2 and 3 both parsed the 1,190-file closure and lowered all 28 functions
in `src/lib/gc_async_mut/gpu/engine2d/color.spl`, then the retained pure-Simple
Stage3 trapped on `field access on nil receiver` and exited 132. Their log
paths are `build/mini_builds/full_cli_admission_cycle2.log` and
`build/mini_builds/full_cli_admission_cycle3.log`; their SHA-256 values are
`024699a05dc5ebcd6452f0539b1f361294679b9a7b3039a7f0a8eee8df5f05ad`
and `c63e11b391f2254971bb767a12f500d2107635ad230e8774528bb138874b68a3`.
The repeated result ended the window at its three-cycle cap. No Stage4 ELF,
Stage5, or smoke result exists; the compatibility bridge remains isolated.

The earlier read-only inference that localized the failure to
`HirLowering.lower_module`'s final diagnostic `eprint` is retained only as
superseded history. The authoritative kernel trap records instruction pointer
`0x559924`. In the retained Stage3 binary this is the `ud2` immediately after
`MethodResolver.resolve_expr` masks its incoming `expr` argument and detects
nil or a low-tag-only value. The normal `rdi=self`, `rsi=expr` register setup
is intact, so the evidence points to an upstream HIR value-representation
error rather than a SysV argument-register error.

`color.spl` still completed all 28 HIR functions. Its first resolution-order
function, `color_black`, ends in `rgb(0, 0, 0)`, providing the concrete Call
tail that reaches the bad boundary. `HirBlock` is desugared as `has: bool`
plus a mandatory `HirExpr`, but ten sites retained the older Option contract:
five consumers matched or unwrapped `block.value` as `Option`, and five
synthetic constructors supplied `Some(...)` or bare `nil`. In particular,
`resolve_block` could extract the Call tail as though it were an Option payload
and pass the resulting nil or low-tag-only value into `resolve_expr`.

Current source integrates the narrow invariant repair: all five consumers gate
on `block.has`; all five constructors provide explicit `has` plus a typed tail
or `NilLit` sentinel; and lowering-error collection uses an indexed loop with
an explicit `LoweringError` binding. Focused regression sources cover the
Call-tail/empty-tail resolution boundary and the constructor/consumer
invariant. Those fixes remain execution-unverified: this correction ran no
test or build, did not rebuild Stage3/Stage4, and did not retry admission. No
Stage4 ELF, Stage5, or essential-tools smoke exists, so the pure-Simple CLI
gate remains blocking and the overall result remains `STATUS: FAIL`.

Independent static review accepted the shaping/material and surface/native
spec stacks after requiring a nonempty selected font identity, explicit
Arabic/Urdu/Hindi direction, and exact Web advance-width propagation through
the proof validator. It rejected the first manifest/distribution rewrite for
private production imports and added heavyweight fixed-`/tmp` unit staging.
The current replacement uses the existing public font-registry APIs, validates
the real immutable bundle root, and rejects an intermediate `assets` symlink
before walking or hashing bundle files. It adds no duplicate facade or staged
font copy. These source-only results remain blocked on the admitted runtime and
do not promote a requirement or NFR.

### Deployed-runtime boundary

- Retain the deployed pure-Simple runtime path and identity used for each
  focused command.
- Reject Rust-seed execution, zero-example results, and unauthenticated
  summaries.
- Do not introduce compiler, interpreter, bootstrap, or bootstrap/runtime
  changes into this goal merely to produce a new runtime.
- Preserve real-device, hosted-WM, performance, and QEMU gates independently
  of focused host execution.

## Requirement matrix

Every non-pass row names its owner, dependency, exact acceptance surface, and
final reviewer. `active` means the owning parallel lane can still change the
row; `blocked` means required runtime/device/manual evidence is unavailable.
The host-independent repair lanes are source-complete but runtime-unverified,
so no row currently has an active writer. Current count: `0 pass`, `0 active`,
`24 blocked`.

Every row below inherits exact immutable retained/refusal paths from its owner:

| Owner token | Focused command and runtime/native refusal root | Generated-manual refusal root |
|---|---|---|
| B manifest/distribution | `build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/` | `build/test-artifacts/shared_multilingual_gpu_fonts/docgen/attempt-$DOCGEN_ATTEMPT/` |
| C shaping/material | `build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/` | `build/test-artifacts/shared_multilingual_gpu_fonts/docgen/attempt-$DOCGEN_ATTEMPT/` |
| D surfaces/SimpleOS | `build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/` | `build/test-artifacts/shared_multilingual_gpu_fonts/docgen/attempt-$DOCGEN_ATTEMPT/` |
| E native/emission/performance | `build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/` (also the E `BUILD_DIR`) | `build/test-artifacts/shared_multilingual_gpu_fonts/docgen/attempt-$DOCGEN_ATTEMPT/` |

Multi-owner rows inherit the union of their owner paths. The
`font_native_perf_audit` and `stage3_hir_lifetime` aliases inherit E; the
REQ-014 F audit reads the B–E union and creates no substitute acceptance
artifact. The production capability rows below override only their live
producer payload paths; their focused command receipts still use the D/E
focused root. An absent path is the exact refusal location, not evidence that
an artifact or hash exists. This mapping supplies every matrix row's
retained/refusal path contract; AC-1 remains active until the final recount.

| Row | Status | Owner / writable scope | Current executable and manual evidence | Dependency and exact completion command | Final reviewer |
|---|---|---|---|---|---|
| REQ-001 | blocked | B manifest/distribution | `shared_font_manifest_spec.spl` and mirror cover pins, order, totals, boundary | deployed pure-Simple runtime; run B command set below | `/root` |
| REQ-002 | blocked | B manifest/distribution | same pair covers decimal contribution, alias policy, deterministic regeneration | deployed pure-Simple runtime; run B command set | `/root` |
| REQ-003 | blocked | B+C manifest/shaping | manifest and shaping acceptance pairs cover sparse states and fail-closed cells | deployed pure-Simple runtime; run B and C command sets | `/root` |
| REQ-004 | blocked | B manifest/distribution | manifest, asset-manifest, installer, archive, SimpleOS bundle/staging specs exist; mirrors exist for the acceptance pairs | deployed pure-Simple runtime; run B command set and zero-stub docgen | `/root` |
| REQ-005 | blocked | B manifest/distribution | manifest and SimpleOS bundle specs cover the pinned candidate catalog and unchanged bytes | deployed pure-Simple runtime; run B command set | `/root` |
| REQ-006 | blocked | C+D shaping/surfaces | `shared_font_surfaces_spec.spl` and legacy Web/GUI/WM route pair cover the shared owner/material seam | deployed pure-Simple runtime; run aggregate and D command sets | `/root` |
| REQ-007 | blocked | C shaping/material | shaping acceptance plus selected Arabic/Devanagari and six integrated GSUB/GPOS unit specs exist; selected-memory binding rejects unregistered paths and path/hash mismatches, and GPOS catalog lookup now rejects duplicate indices without publishing partial adjustments | source is present but runtime-unverified; run the C command set on the deployed pure-Simple runtime and generate six missing unit mirrors | `/root` |
| REQ-008 | blocked | B+C manifest/shaping | manifest and parser/loader specs cover `glyf`, default instance, bitmap, and rejection policy | deployed pure-Simple runtime; run B/C command sets | `/root` |
| REQ-009 | blocked | C+E material/native | renderer, aggregate surface, emission, backend and perf specs contain cache identity/lifecycle oracles | deployed pure-Simple runtime and native record; run C/E sets | `/root` |
| REQ-010 | blocked | E native/emission | GPU emission and CUDA handoff executable/manual pairs cover source/artifact contracts; emission is not execution | deployed pure-Simple runtime; run E source commands; retained native artifact required for promotion | `/root` |
| REQ-011 | blocked | D+E surfaces/native | aggregate surfaces/route plus the six production capability rows below exist; `simple_web_window_renderer_spec.spl` adds fail-closed WmContentFrame font identity/execution/composition and ordered-advance provenance, tamper/missing-origin rejection, and hosted top-frame-only emission; working changes also add fail-closed degenerate Web status, ancestor-clipped nested IMAGE projection, trait/concrete-pixel-buffer and Draw IR/Engine2D clip parity, full-buffer no-nesting parity, and shared nested-collector cases for valid collection plus stale/duplicate/orphan rejection | changes are source-present but runtime-unverified; deployed pure-Simple runtime, hosted frame and QEMU pixels required; complete all six rows below | `/root` |
| REQ-012 | blocked | `font_native_perf_audit` — Simple-side stable physical identity propagation through Engine2D/Engine3D Vulkan owners and immutable native/perf evidence; no Rust runtime/SFFI writes | native readback source contains HUD/world, handles, submit, fence, depth/transform and readback gates; promotion requires durable successful atlas/vertex upload receipts and one discrete/integrated stable UUID/PCI/LUID identity shared by Engine2D and Engine3D | the runtime identity facade is source-present; run `run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_device_metadata_spec.spl`, then on real hardware run `run_focused_spec test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl`; both remain blocked on admitted CLI/core-C | `/root` |
| REQ-013 | blocked | E native 2D/3D/perf | native readback source rejects unavailable, forged, CPU, virtual, and cross-device promotion and fails closed when durable 3D upload receipts are missing | one hardware backend must pass both 2D and 3D through E native command | `/root` |
| REQ-014 | blocked | B–E generation / F audit | among 44 changed/new specs, 19 mirrors are missing, 25 are stale, zero are current, and no retained log proves `0 stubs` | deployed pure-Simple runtime; run all 44 docgen commands below; review manuals | `/root` |
| REQ-015 | blocked | C shaping/material/config | aggregate surfaces and focused config specs cover identity, policies, target order and pre-mutation rejection; working changes canonicalize HIP to ROCm on the prepared batch | batch change is unverified; deployed pure-Simple runtime required; run aggregate/C commands | `/root` |
| REQ-016 | blocked | C shaping/material | source integration covers GSUB 1–8, GPOS 1–9, LookupFlag/GDEF filtering, FeatureVariations, Device/VariationIndex and anchors, named context/data facades, nested contextual remaps, ppem/coordinates/LangSys, pixel/design-unit separation, and fail-closed selected preprocessing; focused regressions cover the reviewed P1s | execute all focused specs on an admitted pure-Simple CLI and regenerate/review all affected manuals | `/root` |
| NFR-001 | blocked | B manifest/distribution | manifest and SimpleOS bundle source gates cover immutable hashes, deterministic generation and corruption rejection | deployed pure-Simple runtime; run B command set | `/root` |
| NFR-002 | blocked | E native/perf | native readback and perf specs define exact packed-ARGB comparison plus broader-AA limits of at most 2 channel levels at edges and 1 coverage level | deployed pure-Simple runtime plus real hardware device; run E perf/native commands | `/root` |
| NFR-003 | blocked | B manifest/distribution | manifest/bundle gates encode the 80 MiB and SimpleOS projection limits | deployed pure-Simple runtime; run B command set | `/root` |
| NFR-004 | blocked | E native/perf | performance spec and manual define warm hit and 1080p/4K p95 thresholds | real device must create a valid immutable `$FOCUSED_ROOT/attempt-$FOCUSED_ATTEMPT/shared_multilingual_gpu_fonts_perf.evidence.env` | `/root` |
| NFR-005 | blocked | E native/perf | performance spec defines equal-semantics 4,096-glyph CPU/GPU comparison | real promoted backend must prove at least 1.25x using E perf command | `/root` |
| NFR-006 | blocked | E native/perf | performance spec defines unchanged upload, RSS delta and GPU high-water checks in the immutable attempt record | real device plus isolated RSS probe; run E perf command | `/root` |
| NFR-007 | blocked | `stage3_hir_lifetime` — runtime fence-wait/wait-idle last-error retention plus symbol/codegen/interpreter/SFFI facade; `font_native_perf_audit` owns only downstream Simple owner/evidence propagation | Engine2D and Engine3D expose retained scalar fault code/mask/sequence, device-loss sequence, identity preservation, and committed CPU-fallback count for real owner paths | exact blocker: `font-owner-device-loss-runtime-proof-unavailable`; the focused native owner-fault trace records device loss false/zero, so native device-loss recovery evidence remains required | `/root` |
| NFR-008 | blocked | E native/perf | native/perf records require shaping through readback/resource stages, successful atlas/vertex upload counts and bytes, exact device identity, and immutable attempt-root retention | retained nonzero upload receipts, handles, fence and device-origin readback required | `/root` |

### REQ-011 production capability rows

The Engine2D row is the shared prerequisite; the other five rows are independent
after it passes. The synced checkout contains no retained current runtime
artifacts at the paths below, so source inspection cannot promote any row.
`run_focused_spec` is the hash-bound helper defined under
[Exact owner commands](#exact-owner-commands); every command waits for Lane A
to admit the exact pure-Simple CLI and core-C identities.

Wave-0 D host readiness is positive but non-promoting. The host has x86_64 and
RV64 QEMU, writable KVM, OVMF/GRUB, clang/llvm-objcopy, hosted-WM capture tools,
mtools/python, and the pinned 1,708,408-byte font with SHA-256
`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
The static-only x86 preflight
`sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs`, hosted-WM
wrapper `--self-test`, and RV64 wrapper `--self-test-wm-font-input` each
reported PASS. They deliberately did not run QEMU or produce acceptance
pixels. A July-27 x86 QEMU PASS under the dirty shared root is rejected: its
source hash is not bound to this feature checkout and 65 of 108 scoped source
files differ. The feature worktree still lacks the hosted binary/current
runtime evidence, x86 feature-bound evidence, RV64 ELF, admitted full CLI, and
reviewed crop pins, so all six rows retain their existing status.

| Capability | Status | Current blocker and retained-artifact state | Exact resume command | Owner / reviewer |
|---|---|---|---|---|
| Engine2D CPU/SIMD plus Vulkan selected-font draw | blocked | No current capture exists under `build/test-artifacts/03_system/app/simple_2d/feature/engine2d_font_surface_verification/`; the tracked native-lane report records hardware discovery only, not a hash-bound device PASS | `run_focused_spec test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl` after Lane A admission on a real Vulkan device | E native / `/root` |
| HTML/WebIR font and browser events | blocked | Canonical production proof `build/test-artifacts/shared_multilingual_gpu_fonts/web/attempt-$WEB_ATTEMPT/aetheric-host-web-gui.env`, `build/test-artifacts/simple-web-font-composition/receipt.env`, and `build/test-artifacts/simple-web-font-rendering-events/evidence.env` are absent; no current submitted-frame/browser-event correlation exists | set `WEB_ATTEMPT`, export `SIMPLE_WEB_FONT_RUN_ID="font-${CHECKPOINT_SHA}-${CLI_SHA}"`, `AETHERIC_HOST_WEB_GUI_SIMPLE_BIN="$CLI"`, and `AETHERIC_HOST_WEB_GUI_PROOF="$PWD/build/test-artifacts/shared_multilingual_gpu_fonts/web/attempt-$WEB_ATTEMPT/aetheric-host-web-gui.env"`, then `run_focused_spec test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl` | D surfaces / `/root` |
| GUI widget-tree font and events | blocked | `build/test-artifacts/03_system/gui/feature/gui_font_event_surface/gui_font_event.txt` is absent; source assertions and a CPU mirror are not production evidence | `run_focused_spec test/03_system/gui/feature/gui_font_event_surface_spec.spl` after Lane A admission | D surfaces / `/root` |
| Linux hosted WM live window | blocked | `build/linux-hosted-wm-font-event-current/evidence.env` and `report.md` are absent; a current X11/winit frame and reviewed glyph pin are required | `BUILD_DIR=build/linux-hosted-wm-font-event-current REPORT_PATH=build/linux-hosted-wm-font-event-current/report.md SIMPLE_BIN="$CLI" sh scripts/check/check-linux-hosted-wm-live-window-evidence.shs`, then `run_focused_spec test/03_system/gui/linux_hosted_wm_live_window_spec.spl` | D surfaces / `/root` |
| x86_64 SimpleOS QEMU WM | blocked | `build/test-simpleos-wm-fullscreen-live/evidence.env`, report, framebuffer captures, and font crop are absent. `/home/ormastes/dev/pub/simple/build/simpleos_wm_fullscreen_evidence/evidence.env` is explicitly rejected because its dirty-root source snapshot differs from this feature checkout in 65/108 scoped files | `export SIMPLE_BIN="$CLI"; run_focused_spec test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl`; the spec runs the live wrapper exactly once | D SimpleOS / `/root` |
| RV64 SimpleOS QEMU WM | blocked | Canonical live root `build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live/` lacks the retained report, QMP scanout, input transcript, and reviewed RV64-only crop pin; `build/os/fat32-riscv64-desktop.img` exists at exactly 134217728 bytes, but the RV64 ELF remains absent | export `BUILD_DIR=build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live`, `REPORT_PATH="$BUILD_DIR/report.md"`, the exact `RV64_DISPLAY_SMOKE_ELF`, `RV64_WM_FONT_DISK`, and reviewed `RV64_WM_FONT_REGION_EXPECTED_SHA256`, then `run_focused_spec test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl`; the spec runs the live wrapper exactly once | D SimpleOS / `/root` |

No row is classified `pass`: static source, an existing Markdown file, emitted
source, CPU mirror, simulation, or a crashed command cannot prove the selected
runtime/native requirement.

## Canonical executable/manual audit

The authoritative inventory contains 44 executable specs changed or added since
`origin/main`, after excluding the compiler-only specs and adding the focused
runner contract, SimpleOS producer/consumer artifact-root contract, four
REQ-016 full-layout specs, changed selected-Devanagari policy spec, and seven
retained font source-contract specs from the current owner overlay, plus the
Engine2D runtime-config, Draw IR execution-receipt, and REQ-011 Simple Web
window-renderer contracts. Nineteen mirrored manuals are missing, 25 are present but stale, zero are
current, and zero retained owner docgen `{out,err}` files exist. Therefore all
44 require focused deployed-runtime docgen
and zero manuals have accepted current `0 stubs` evidence.

The eleven original acceptance specs are accounted for, but their mirrors are
not all current: `install_font_assets_spec.md` lacks one current scenario title,
and every assigned mirror still requires fresh zero-stub docgen evidence. The
production-surface acceptance mirrors exist for:

- `web_font_rendering_surface_spec`
- `gui_font_event_surface_spec`
- `linux_hosted_wm_live_window_spec`
- `simpleos_wm_fullscreen_spec`
- `rv64_simpleos_wm_font_input_spec`

`production_gui_font_runtime_evidence_spec.spl` is supporting backend/runtime
evidence, not an independent REQ-011 producer acceptance row; its absent manual
does not replace any canonical pair.

Nineteen changed/new specs currently lack mirrors:

- `doc/06_spec/01_unit/lib/test_runner_result_wrapper_spec.md`
- `doc/06_spec/01_unit/lib/common/text_layout/font_render_config_spec.md`
- `doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_result_spec.md`
- `doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_font_scalar_receipt_spec.md`
- `doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_device_metadata_spec.md`
- `doc/06_spec/01_unit/lib/gpu/engine2d/font_runtime_config_spec.md`
- `doc/06_spec/01_unit/lib/gpu/engine3d/font_compat_spec.md`
- `doc/06_spec/01_unit/lib/gpu/engine3d/font_hud_material_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_apply_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_gsub_full_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_gpos_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_gpos_full_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_gpos_variation_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_lookup_flags_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_pinned_inventory_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_parser_layout_selector_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_parser_spec.md`
- `doc/06_spec/01_unit/lib/skia/shaper_spec.md`
- `doc/06_spec/02_integration/rendering/wm_nested_content_frame_spec.md`

Twenty-five existing mirrors are stale because their executable sources changed in this
all-items worktree and no current pure-Simple docgen result exists:

- `install_font_assets_spec.md`
- `release_archive_layout_spec.md`
- `font_asset_manifest_spec.md`
- `font_renderer_spec.md`
- `shared_multilingual_gpu_fonts_perf_evidence_spec.md`
- `backend_vulkan_font_spec.md`
- `draw_ir_adv_spec.md`
- `gui_entry_desktop_production_render_contract_spec.md`
- `hosted_entry_live_proof_focus_contract_spec.md`
- `simpleos_font_asset_staging_spec.md`
- `simpleos_font_bundle_spec.md`
- `legacy_web_gui_wm_font_route_spec.md`
- `native_gpu_font_readback_spec.md`
- `shared_font_manifest_spec.md`
- `shared_font_shaping_acceptance_spec.md`
- `shared_font_surfaces_spec.md`
- `web_font_rendering_surface_spec.md`
- `gui_font_event_surface_spec.md`
- `linux_hosted_wm_live_window_spec.md`
- `simpleos_wm_fullscreen_spec.md`
- `rv64_simpleos_wm_font_input_spec.md`
- `selected_devanagari_spec.md`
- `simpleos_wm_qemu_evidence_contract_spec.md`
- `shared_multilingual_gpu_fonts_perf_spec.md`
- `simple_web_window_renderer_spec.md`

The aggregate `shared_font_surfaces_spec.spl` now uses the frozen
`step("Prepare one shared font batch for 2D and 3D")`; its mirror is stale until
canonical regeneration. The perf owner likewise changed to the frozen
`step("Measure warm font rendering and resource bounds")`; its mirror remains
stale until canonical regeneration. Hand edits cannot substitute for docgen.

Static scans found no `pass_todo`, `expect(true).to_equal(true)`,
`pass_do_nothing`, or `pass_dn` in the aggregate acceptance specs.
`find doc/06_spec -name '*_spec.spl' -print` returned no paths. These are static
checks only.

The current HIP-to-ROCm batch, degenerate-Web fail-closed, nested WM IMAGE, and
shared nested-frame collector changes remain unverified implementation evidence.
The collector's source spec covers a valid reachable collection plus
fail-closed stale, duplicate, and orphan rejection; its mirror is missing and
the behavioral cases have not run on an admitted CLI.

### Lane F static source/manual-quality audit

The retained pre-REQ-016 audit found no `pass_todo`, tautological
`expect(true).to_equal(true)`, `to_raise`, or empty scenario body. Its
scenario/expect counts predate the four REQ-016 specs and the changed
selected-Devanagari policy spec and omitted the two evidence-contract specs, so
they are not current 44-source evidence; lane F must audit all 44 sources after
an admitted runtime is available.
The four `pass_do_nothing` calls in
`wm_nested_content_frame_spec.spl` are explicitly justified no-op methods on
the pixel-only fixture (`draw_text`, `draw_char_8x16`, `present`, and
`present_rect`), not scenario passes.

All eight frozen manual steps remain present in their owning acceptance sources:
manifest load, exact-face shaping, shared 2D/3D batch preparation, portable
emission, native submission/readback, legacy Web/GUI/WM Draw IR, SimpleOS pixel
capture, and warm rendering/resource measurement.

Lane C resolved all 19 previously reported noncanonical matchers. It also
repaired two short-expression parse defects: the split GSUB context-rule
inequality in `ot_layout_apply.spl`, and wrapped boolean continuations in the
canonical layout shaper. These are source-present but runtime-unverified.

The selected-memory binder now accepts parsed bytes only when the fallback
primary has no live handle, its path is an exact selected-registry path, and
the registry identity starts with the parsed blob's exact SHA-256 plus its
axis identity. Arbitrary paths and selected-path/mismatched-byte combinations
remain unbound. This hardening and its direct regression are also
source-present but runtime-unverified.

The pinned GSUB/GPOS support map is deliberately narrow:

The full REQ-016 audit rejects the former pinned-map completion claim. The
merged baseline implements GSUB 1–8 and GPOS 1–9 with split subtable owners,
fixes the context-format-3 input increment, admits all defined LookupFlag/GDEF
filters, evaluates supported FeatureVariations, and decodes
Device/VariationIndex plus anchor formats 2/3. ExtensionSubst rejects a nested
type-7 target, as required by the OpenType extension contract. The selected
high-level complex-script boundary remains fail-closed outside explicitly
supported preprocessing; the complete lower-level GSUB/GPOS executor does not
turn that boundary into a claim of general Indic preprocessing. Source review
then closed the production gaps: one shared GPOS data context/budget reaches
validation, nested dispatch, and application; PairPos resolves Device offsets
from its owning subtable; packed Device pixels remain post-scale while
VariationIndex stays in design units; public shaping forwards normalized
coordinates and LangSys; GSUB preserves device fields; and contextual edits
compose old-to-new position maps. Focused source regressions exist, but no
full-layout claim is valid until they execute on the admitted runtime.

The four new full-layout specs, changed selected-Devanagari policy spec, focused
runner contract, and SimpleOS artifact-root contract established the prior
scope; the retained current-overlay, Draw IR execution-receipt, and Simple Web
window-renderer contracts raise it to 44 manuals: 19 mirrors are absent and 25 are
stale. The previous title-coverage split is invalidated by the newly changed
specs. `font_asset_manifest_spec.md` and
`gui_entry_desktop_production_render_contract_spec.md` explicitly identify
themselves as manually synchronized/docgen-pending. Hand synchronization is not
generated evidence. The 19 absent mirrors and all 23 stale mirrors therefore
remain rejected until deterministic docgen succeeds with `0 stubs`.

Fourteen additional changed compiler/bootstrap specs are prerequisite-enablement
regressions, not shared-font requirement evidence, and are explicitly excluded
from the 44-manual and 48-command font graphs:
`bootstrap_main_source_spec.spl`,
`cli_native_build_main_contract_spec.spl`,
`interpreter_backend_spec.spl`,
`hir_lowering_error_collection_spec.spl`,
`bootstrap_expr_stmt_arena_spec.spl`,
`hir_block_tail_invariants_source_spec.spl`,
`const_eval_spec.spl`,
`effect_inference_spec.spl`, and
`resolve_nil_guard_spec.spl`,
`bootstrap_focused_native_build_spec.spl`,
`bootstrap_context_mir_source_spec.spl`,
`option_variant_order_source_spec.spl`,
`resolve_import_symbols_spec.spl`, and
`symbol_display_name_spec.spl`. All five canonical prerequisite mirrors are
missing:
`doc/06_spec/01_unit/app/cli/bootstrap_focused_native_build_spec.md`,
`doc/06_spec/01_unit/compiler/driver/bootstrap_context_mir_source_spec.md`,
`doc/06_spec/01_unit/compiler/mir/option_variant_order_source_spec.md`,
`doc/06_spec/01_unit/compiler/hir/resolve_import_symbols_spec.md`, and
`doc/06_spec/01_unit/compiler/hir/symbol_display_name_spec.md`. The stale
legacy-path copy at
`doc/06_spec/test/01_unit/compiler/hir/resolve_import_symbols_spec.md` does not
satisfy the canonical docgen path. During this audit, two apparent further diffs
came only from newer upstream GPU-wire changes:
`processing_cpu_fallback_daemon_wire_spec.spl` and
`simpleos_qemu_host_gpu_2d_spec.spl`. Neither contains a font or glyph
acceptance row, neither is branch-authored shared-font evidence, and both are
excluded from this scope; the completion-time rebase absorbs that upstream
drift. Thus those two upstream-only specs remain excluded; the seven retained
current-overlay contracts set the authoritative feature scope to 44.

## Exact owner commands

The authoritative docgen scope is the 44 changed/new specs classified above.
Each source owner retains the command, stdout, stderr, exit, and output-manual
hash under an immutable attempt directory; lane F audits all 44.

All retained paths are below
`build/test-artifacts/shared_multilingual_gpu_fonts/`. The exact deterministic
input set and immutable runner are frozen below. This command has not been run
and does not imply generated evidence:

```bash
set -euo pipefail
: "${CLI:?set CLI to the deployed pure-Simple runtime}"
: "${CLI_SHA:?set CLI_SHA to the admitted CLI SHA-256}"
: "${CORE_C_DIR:?set CORE_C_DIR to the matching core-C directory}"
: "${CORE_C_SHA:?set CORE_C_SHA to the admitted core-C archive SHA-256}"
: "${CHECKPOINT_SHA:?set CHECKPOINT_SHA to the clean source checkpoint}"
: "${DOCGEN_ATTEMPT:=1}"
case "$DOCGEN_ATTEMPT" in
  1|2|3) ;;
  *) echo "invalid docgen attempt: $DOCGEN_ATTEMPT" >&2; exit 2 ;;
esac
[ "$(git rev-parse HEAD)" = "$CHECKPOINT_SHA" ]
[ -z "$(git status --porcelain --untracked-files=normal)" ]
[ "$(sha256sum "$CLI" | awk '{print $1}')" = "$CLI_SHA" ]
[ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" = "$CORE_C_SHA" ]
DOCGEN_ROOT="build/test-artifacts/shared_multilingual_gpu_fonts/docgen/attempt-$DOCGEN_ATTEMPT"
mkdir -p "$DOCGEN_ROOT"

run_docgen_spec() {
  spec=$1
  name=${spec#test/}
  name=${name//\//_}
  manual="doc/06_spec/${spec#test/}"
  manual=${manual%.spl}.md
  base="$DOCGEN_ROOT/$name"
  for suffix in command out err exit manual.sha256; do
    if [ -e "$base.$suffix" ]; then
      echo "refusing duplicate docgen execution: $spec" >&2
      return 125
    fi
  done
  spec_sha=$(sha256sum "$spec" | awk '{print $1}')
  manual_before=missing
  if [ -f "$manual" ]; then
    manual_before=$(sha256sum "$manual" | awk '{print $1}')
  fi
  {
    printf 'checkpoint_sha=%s\ncheckpoint_clean=true\nattempt=%s\n' \
      "$CHECKPOINT_SHA" "$DOCGEN_ATTEMPT"
    printf 'cli=%s\ncli_sha256=%s\n' "$CLI" "$CLI_SHA"
    printf 'core_c_dir=%s\ncore_c_sha256=%s\n' "$CORE_C_DIR" "$CORE_C_SHA"
    printf 'spec=%s\nspec_sha256=%s\n' "$spec" "$spec_sha"
    printf 'manual=%s\nmanual_before_sha256=%s\n' "$manual" "$manual_before"
    printf 'command'
    printf ' %q' "$CLI" spipe-docgen "$spec" --output doc/06_spec --no-index
    printf '\n'
  } >"$base.command"
  if [ "$(sha256sum "$CLI" | awk '{print $1}')" != "$CLI_SHA" ] ||
      [ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" != "$CORE_C_SHA" ]; then
    rc=1
    : >"$base.out"
    printf '%s\n' "admitted CLI/core-C changed before docgen" >"$base.err"
  elif "$CLI" spipe-docgen "$spec" --output doc/06_spec --no-index \
      >"$base.out" 2>"$base.err"; then
    rc=0
  else
    rc=$?
  fi
  if [ "$rc" -eq 0 ] &&
      ! grep -Fqx 'DONE Generated 1 docs (1 complete, 0 stubs)' "$base.out"; then
    rc=1
  fi
  if [ "$rc" -eq 0 ] && [ ! -f "$manual" ]; then
    rc=1
  fi
  manual_after=missing
  if [ "$rc" -eq 0 ]; then
    manual_after=$(sha256sum "$manual" | awk '{print $1}')
  fi
  if [ "$rc" -eq 0 ] &&
      { [ "$(sha256sum "$spec" | awk '{print $1}')" != "$spec_sha" ] ||
        [ "$(sha256sum "$CLI" | awk '{print $1}')" != "$CLI_SHA" ] ||
        [ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" != "$CORE_C_SHA" ]; }; then
    rc=1
  fi
  if [ "$rc" -eq 0 ]; then
    printf 'manual_sha256=%s\n' \
      "$manual_after" >"$base.manual.sha256"
  fi
  printf '%s\n' "$rc" >"$base.exit"
  if [ "$rc" -ne 0 ]; then
    return "$rc"
  fi
}

while IFS= read -r spec; do
  run_docgen_spec "$spec"
done <<'SPECS'
test/01_unit/app/release/install_font_assets_spec.spl
test/01_unit/app/release/release_archive_layout_spec.spl
test/01_unit/lib/common/encoding/font_asset_manifest_spec.spl
test/01_unit/lib/common/text_layout/font_render_config_spec.spl
test/01_unit/lib/common/text_layout/font_renderer_spec.spl
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_result_spec.spl
test/01_unit/helpers/shared_multilingual_gpu_fonts_perf_evidence_spec.spl
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_font_scalar_receipt_spec.spl
test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_device_metadata_spec.spl
test/01_unit/lib/gpu/engine2d/font_runtime_config_spec.spl
test/01_unit/lib/gpu/engine3d/font_compat_spec.spl
test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl
test/01_unit/lib/test_runner_result_wrapper_spec.spl
test/01_unit/lib/skia/ot_layout_apply_spec.spl
test/01_unit/lib/skia/ot_layout_gsub_full_spec.spl
test/01_unit/lib/skia/ot_layout_gpos_spec.spl
test/01_unit/lib/skia/ot_layout_gpos_full_spec.spl
test/01_unit/lib/skia/ot_layout_gpos_variation_spec.spl
test/01_unit/lib/skia/ot_layout_lookup_flags_spec.spl
test/01_unit/lib/skia/ot_layout_pinned_inventory_spec.spl
test/01_unit/lib/skia/ot_parser_layout_selector_spec.spl
test/01_unit/lib/skia/ot_parser_spec.spl
test/01_unit/lib/skia/selected_devanagari_spec.spl
test/01_unit/lib/skia/shaper_spec.spl
test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl
test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl
test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl
test/01_unit/os/compositor/simple_web_window_renderer_spec.spl
test/01_unit/os/port/simpleos_font_bundle_spec.spl
test/02_integration/os/port/simpleos_font_asset_staging_spec.spl
test/02_integration/rendering/wm_nested_content_frame_spec.spl
test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl
test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl
test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl
test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl
test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl
test/03_system/gui/feature/gui_font_event_surface_spec.spl
test/03_system/gui/linux_hosted_wm_live_window_spec.spl
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl
test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl
test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl
SPECS

DOCGEN_ROOT="build/test-artifacts/shared_multilingual_gpu_fonts/compiler-perf-prerequisite-docgen/attempt-$DOCGEN_ATTEMPT"
mkdir -p "$DOCGEN_ROOT"
while IFS= read -r spec; do
  run_docgen_spec "$spec"
done <<'SPECS'
test/01_unit/app/cli/bootstrap_focused_native_build_spec.spl
test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl
test/01_unit/compiler/mir/option_variant_order_source_spec.spl
test/01_unit/compiler/hir/resolve_import_symbols_spec.spl
test/01_unit/compiler/hir/symbol_display_name_spec.spl
SPECS
```

Lane A records the deployed pure-Simple runtime and matching core-C identity
used for focused checks. Rust-seed Stage2 generation remains non-evidence and
is not permitted in this exhausted producer window; bounded seed diagnostics
remain non-acceptance only. A Rust binary or exit `2`, `124`, `132`, or `139`
is never acceptance evidence. Stage 2 provenance writer/verifier wiring is
source-present, but no current Stage 2 manifest and sidecar have been emitted
and verified. Stage 4 admission requires
`scripts/check/stage4-provenance-receipt.shs check` to pass and the receipt plus
sidecar identities to be sealed by essential-tools and the aggregate; the
helper's presence alone is not evidence.

The current window is exhausted and this block is documentation, not
authorization to execute. In a fresh bounded producer window, the fail-fast
Option gate requires all of these pinned inputs and two new, disjoint roots:

```bash
: "${SIMPLE_BIN:?pure-Simple Stage 2 path}"
: "${SIMPLE_BIN_SHA:?Stage 2 SHA-256}"
: "${STAGE2_PROVENANCE_PATH:?Stage 2 manifest path}"
: "${STAGE2_PROVENANCE_SHA:?Stage 2 manifest SHA-256}"
: "${CHECKPOINT_SHA:?clean checkpoint}"
: "${CORE_C_DIR:?core-C capsule directory}"
: "${CORE_C_SHA:?core-C archive SHA-256}"
: "${CORE_C_MANIFEST_SHA:?core-C manifest SHA-256}"
: "${OPTION_ADMISSION_ATTEMPT_ROOT:?new sealed receipt root}"
: "${OPTION_ADMISSION_CACHE_ROOT:?new cache root outside the receipt root}"
scripts/check/check-native-option-admission-probes.shs
```

Only A → B → C success permits Stage 3 and incremental Stage 4. The resulting
full CLI is admitted only after:

```bash
sh scripts/check/stage4-provenance-receipt.shs check \
  "$STAGE4_RECEIPT_PATH" "$STAGE4_RECEIPT_SHA256" "$CLI"
```

After lane A publishes those immutable values, set:

```bash
CLI=/absolute/path/to/deployed/pure-simple
CLI_SHA=<deployed-cli-sha256>
CORE_C_DIR=/absolute/path/to/deployed/core-c
CORE_C_SHA=<deployed-libsimple_runtime.a-sha256>
CHECKPOINT_SHA=$(git rev-parse HEAD)
```

Lane A first runs the shared essential-tools admission gate against that exact
binary and retains both streams:

```bash
set -euo pipefail
ESSENTIAL_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/essential-tools
mkdir -p "$ESSENTIAL_ROOT"
for artifact in \
    identity.env command out err exit summary.env evidence.sha256; do
  if [ -e "$ESSENTIAL_ROOT/$artifact" ]; then
    echo "refusing duplicate essential-tools admission: $ESSENTIAL_ROOT/$artifact" >&2
    exit 125
  fi
done
[ "$(git rev-parse HEAD)" = "$CHECKPOINT_SHA" ]
[ -z "$(git status --porcelain --untracked-files=normal)" ]
CLI_ACTUAL_SHA=$(sha256sum "$CLI" | awk '{print $1}')
[ "$CLI_ACTUAL_SHA" = "$CLI_SHA" ]
CORE_C_ACTUAL_SHA=$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')
[ "$CORE_C_ACTUAL_SHA" = "$CORE_C_SHA" ]
{
  printf 'checkpoint_sha=%s\ncheckpoint_clean=true\n' "$CHECKPOINT_SHA"
  printf 'cli=%s\ncli_sha256=%s\n' "$CLI" "$CLI_SHA"
  printf 'core_c_dir=%s\ncore_c_sha256=%s\n' "$CORE_C_DIR" "$CORE_C_SHA"
} >"$ESSENTIAL_ROOT/identity.env"
{
  printf 'command env SIMPLE_BINARY=%q sh %q\n' \
    "$CLI" scripts/check/check-bootstrap-essential-tools-smoke.shs
} >"$ESSENTIAL_ROOT/command"
if SIMPLE_BINARY="$CLI" sh scripts/check/check-bootstrap-essential-tools-smoke.shs \
    >"$ESSENTIAL_ROOT/out" 2>"$ESSENTIAL_ROOT/err"; then
  essential_rc=0
else
  essential_rc=$?
fi
printf '%s\n' "$essential_rc" >"$ESSENTIAL_ROOT/exit"
[ "$essential_rc" -eq 0 ]
[ "$(sha256sum "$CLI" | awk '{print $1}')" = "$CLI_SHA" ]
[ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" = "$CORE_C_SHA" ]
for marker in \
    essential_test_runner_smoke=true \
    essential_lint_smoke=true \
    essential_duplicate_checker_smoke=true \
    bootstrap_essential_tools_smoke=true; do
  [ "$(grep -Fxc "$marker" "$ESSENTIAL_ROOT/out")" -eq 1 ]
done
printf 'status=pass\n' >"$ESSENTIAL_ROOT/summary.env"
(
  cd "$ESSENTIAL_ROOT"
  sha256sum identity.env command out err exit summary.env
) >"$ESSENTIAL_ROOT/evidence.sha256"
```

The command must exit zero and its retained stdout must contain
`essential_test_runner_smoke=true`, `essential_lint_smoke=true`,
`essential_duplicate_checker_smoke=true`, and
`bootstrap_essential_tools_smoke=true`. A wrapper, Rust seed, stale hash, or
missing marker is not admission.

The essential-tools gate already executes the clean lint and duplicate-check
probes and validates their exact success markers. Do not run those unchanged
commands a second time; the retained gate streams are the one admission record.

Lane A calibrates the runner once globally before any focused result:

```bash
set -euo pipefail
CAL_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration
mkdir -p "$CAL_ROOT"
for artifact in \
    identity.env fail.command fail.out fail.err fail.exit \
    empty.command empty.out empty.err empty.exit summary.env evidence.sha256; do
  if [ -e "$CAL_ROOT/$artifact" ]; then
    echo "refusing duplicate runner calibration: $CAL_ROOT/$artifact" >&2
    exit 125
  fi
done
[ "$(git rev-parse HEAD)" = "$CHECKPOINT_SHA" ]
[ -z "$(git status --porcelain --untracked-files=normal)" ]
CORE_C_ACTUAL_SHA=$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')
[ "$CORE_C_ACTUAL_SHA" = "$CORE_C_SHA" ]
RUNNER_SHA=$(sha256sum src/app/test/font_evidence_runner.spl | awk '{print $1}')
FAIL_FIXTURE_SHA=$(sha256sum scripts/check/fixtures/font_evidence_runner_fail_spec.spl | awk '{print $1}')
EMPTY_FIXTURE_SHA=$(sha256sum scripts/check/fixtures/font_evidence_runner_empty_spec.spl | awk '{print $1}')
{
  printf 'checkpoint_sha=%s\ncheckpoint_clean=true\n' "$CHECKPOINT_SHA"
  printf 'cli=%s\ncli_sha256=%s\n' "$CLI" "$CLI_SHA"
  printf 'core_c_dir=%s\ncore_c_sha256=%s\n' "$CORE_C_DIR" "$CORE_C_SHA"
  printf 'runner_sha256=%s\n' "$RUNNER_SHA"
  printf 'fail_fixture_sha256=%s\nempty_fixture_sha256=%s\n' \
    "$FAIL_FIXTURE_SHA" "$EMPTY_FIXTURE_SHA"
} >"$CAL_ROOT/identity.env"

record_command() {
  output=$1
  shift
  {
    printf 'command'
    printf ' %q' "$@"
    printf '\n'
  } >"$output"
}

record_command "$CAL_ROOT/fail.command" \
  "$CLI" run src/app/test/font_evidence_runner.spl -- \
  "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
  scripts/check/fixtures/font_evidence_runner_fail_spec.spl
if "$CLI" run src/app/test/font_evidence_runner.spl -- \
    "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
    scripts/check/fixtures/font_evidence_runner_fail_spec.spl \
    >"$CAL_ROOT/fail.out" 2>"$CAL_ROOT/fail.err"; then
  fail_rc=0
else
  fail_rc=$?
fi
printf '%s\n' "$fail_rc" >"$CAL_ROOT/fail.exit"

record_command "$CAL_ROOT/empty.command" \
  "$CLI" run src/app/test/font_evidence_runner.spl -- \
  "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
  scripts/check/fixtures/font_evidence_runner_empty_spec.spl
if "$CLI" run src/app/test/font_evidence_runner.spl -- \
    "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
    scripts/check/fixtures/font_evidence_runner_empty_spec.spl \
    >"$CAL_ROOT/empty.out" 2>"$CAL_ROOT/empty.err"; then
  empty_rc=0
else
  empty_rc=$?
fi
printf '%s\n' "$empty_rc" >"$CAL_ROOT/empty.exit"

[ "$fail_rc" -eq 1 ]
[ "$empty_rc" -eq 1 ]
grep -Fqx 'error: test-runner: spec failed' "$CAL_ROOT/fail.out"
grep -Fqx 'error: test-runner: no examples executed' "$CAL_ROOT/empty.out"
{
  printf 'status=pass\n'
  printf 'fail_exit=1\nempty_exit=1\n'
} >"$CAL_ROOT/summary.env"
(
  cd "$CAL_ROOT"
  sha256sum \
    identity.env fail.command fail.out fail.err fail.exit \
    empty.command empty.out empty.err empty.exit summary.env
) >"$CAL_ROOT/evidence.sha256"
```

The first command must exit 1 with `test-runner: spec failed`; the second must
exit 1 with `test-runner: no examples executed`. Retain both logs and the exact
command lines under
`build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/`.
Lanes B–E reference that one immutable calibration set; they do not rerun it.

Every focused spec uses the same hash-bound runner:
`src/app/test/font_evidence_runner.spl` forwards only the ten reviewed native
variables: `SIMPLE_BIN`, `SIMPLE_BINARY`, `SIMPLE_WEB_FONT_RUN_ID`,
`AETHERIC_HOST_WEB_GUI_SIMPLE_BIN`, `AETHERIC_HOST_WEB_GUI_PROOF`, `BUILD_DIR`,
`REPORT_PATH`, `RV64_DISPLAY_SMOKE_ELF`, `RV64_WM_FONT_DISK`, and
`RV64_WM_FONT_REGION_EXPECTED_SHA256`. It does not forward arbitrary ambient
host state.

```bash
set -euo pipefail
: "${CLI:?set CLI to the admitted pure-Simple runtime}"
: "${CLI_SHA:?set CLI_SHA to the admitted CLI SHA-256}"
: "${CORE_C_DIR:?set CORE_C_DIR to the matching core-C directory}"
: "${CORE_C_SHA:?set CORE_C_SHA to the admitted core-C archive SHA-256}"
: "${CHECKPOINT_SHA:?set CHECKPOINT_SHA to the clean source checkpoint}"
[ "$(git rev-parse HEAD)" = "$CHECKPOINT_SHA" ]
[ -z "$(git status --porcelain --untracked-files=normal)" ]
[ "$(sha256sum "$CLI" | awk '{print $1}')" = "$CLI_SHA" ]
[ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" = "$CORE_C_SHA" ]
RUNNER_SOURCE=src/app/test/font_evidence_runner.spl
RUNNER_SHA=$(sha256sum "$RUNNER_SOURCE" | awk '{print $1}')
FOCUSED_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/focused
FOCUSED_ATTEMPT=${FOCUSED_ATTEMPT:-1}
case "$FOCUSED_ATTEMPT" in
  1|2|3) ;;
  *) echo "invalid focused attempt: $FOCUSED_ATTEMPT" >&2; exit 2 ;;
esac

run_focused_spec() {
  spec=$1
  if [ "$(git rev-parse HEAD)" != "$CHECKPOINT_SHA" ] ||
      [ -n "$(git status --porcelain --untracked-files=normal)" ]; then
    echo "refusing focused execution outside the clean checkpoint: $spec" >&2
    return 126
  fi
  name=${spec#test/}
  name=${name//\//_}
  spec_sha=$(sha256sum "$spec" | awk '{print $1}')
  root="$FOCUSED_ROOT/attempt-$FOCUSED_ATTEMPT"
  mkdir -p "$root"
  for suffix in command out err exit; do
    if [ -e "$root/$name.$suffix" ]; then
      echo "refusing duplicate focused execution: $spec" >&2
      return 125
    fi
  done
  {
    printf 'checkpoint_sha=%s\ncheckpoint_clean=true\nattempt=%s\n' \
      "$CHECKPOINT_SHA" "$FOCUSED_ATTEMPT"
    printf 'spec=%s\nspec_sha256=%s\nrunner_sha256=%s\n' \
      "$spec" "$spec_sha" "$RUNNER_SHA"
    printf 'cli=%s\ncli_sha256=%s\ncore_c_dir=%s\ncore_c_sha256=%s\n' \
      "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA"
    printf 'SIMPLE_BIN=%s\nSIMPLE_WEB_FONT_RUN_ID=%s\n' \
      "${SIMPLE_BIN:-}" "${SIMPLE_WEB_FONT_RUN_ID:-}"
    printf 'SIMPLE_BINARY=%s\nAETHERIC_HOST_WEB_GUI_SIMPLE_BIN=%s\n' \
      "${SIMPLE_BINARY:-}" "${AETHERIC_HOST_WEB_GUI_SIMPLE_BIN:-}"
    printf 'AETHERIC_HOST_WEB_GUI_PROOF=%s\n' \
      "${AETHERIC_HOST_WEB_GUI_PROOF:-}"
    printf 'BUILD_DIR=%s\nREPORT_PATH=%s\n' \
      "${BUILD_DIR:-}" "${REPORT_PATH:-}"
    printf 'RV64_DISPLAY_SMOKE_ELF=%s\nRV64_WM_FONT_DISK=%s\n' \
      "${RV64_DISPLAY_SMOKE_ELF:-}" "${RV64_WM_FONT_DISK:-}"
    printf 'RV64_WM_FONT_REGION_EXPECTED_SHA256=%s\n' \
      "${RV64_WM_FONT_REGION_EXPECTED_SHA256:-}"
    printf 'command'
    printf ' %q' "$CLI" run src/app/test/font_evidence_runner.spl -- \
      "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" "$spec"
    printf '\n'
  } >"$root/$name.command"
  if "$CLI" run src/app/test/font_evidence_runner.spl -- \
      "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" "$spec" \
      >"$root/$name.out" 2>"$root/$name.err"; then
    rc=0
  else
    rc=$?
  fi
  if [ "$(git rev-parse HEAD)" != "$CHECKPOINT_SHA" ] ||
      [ -n "$(git status --porcelain --untracked-files=normal)" ]; then
    rc=1
  fi
  if [ "$rc" -eq 0 ] &&
      { [ "$(sha256sum "$spec" | awk '{print $1}')" != "$spec_sha" ] ||
        [ "$(sha256sum "$RUNNER_SOURCE" | awk '{print $1}')" != "$RUNNER_SHA" ] ||
        [ "$(sha256sum "$CLI" | awk '{print $1}')" != "$CLI_SHA" ] ||
        [ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" != "$CORE_C_SHA" ]; }; then
    rc=1
  fi
  if [ "$rc" -eq 0 ] &&
      ! grep -Fq 'test-runner: native result wrapper complete' "$root/$name.out"; then
    rc=1
  fi
  native_trace=
  if [ "$spec" = \
      test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl ]; then
    native_trace="$root/native_gpu_font_readback.evidence.env"
    [ -f "$native_trace" ] || rc=1
  fi
  printf '%s\n' "$rc" >"$root/$name.exit"
  {
    printf 'stdout_sha256=%s\n' \
      "$(sha256sum "$root/$name.out" | awk '{print $1}')"
    printf 'stderr_sha256=%s\n' \
      "$(sha256sum "$root/$name.err" | awk '{print $1}')"
    printf 'exit_sha256=%s\n' \
      "$(sha256sum "$root/$name.exit" | awk '{print $1}')"
    if [ -n "$native_trace" ] && [ -f "$native_trace" ]; then
      printf 'native_trace_path=%s\nnative_trace_sha256=%s\n' \
        "$native_trace" "$(sha256sum "$native_trace" | awk '{print $1}')"
    fi
  } >>"$root/$name.command"
  if [ "$rc" -ne 0 ]; then
    return "$rc"
  fi
}
```

Attempt 1 is the only initial execution. Attempts 2 and 3 are reserved for an
owner repair that changes the failing source; an unchanged green or unchanged
failure is never rerun. The command, both streams, and exit code remain
immutable under the attempt directory. Focused execution starts from the clean
checkpoint before docgen writes any manuals.

Before any lane relies on the helper, run its changed source contract once:

```bash
run_focused_spec test/01_unit/lib/test_runner_result_wrapper_spec.spl
```

Lane B executes once each:

```bash
run_focused_spec test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl
run_focused_spec test/01_unit/app/release/install_font_assets_spec.spl
run_focused_spec test/01_unit/app/release/release_archive_layout_spec.spl
run_focused_spec test/01_unit/lib/common/encoding/font_asset_manifest_spec.spl
run_focused_spec test/01_unit/os/port/simpleos_font_bundle_spec.spl
run_focused_spec test/02_integration/os/port/simpleos_font_asset_staging_spec.spl
```

Lane C executes the aggregate and integrated shaping gates once each:

```bash
run_focused_spec test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_apply_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_gsub_full_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_gpos_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_gpos_full_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_gpos_variation_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_lookup_flags_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_pinned_inventory_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_parser_layout_selector_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_parser_spec.spl
run_focused_spec test/01_unit/lib/skia/shaper_spec.spl
run_focused_spec test/01_unit/lib/skia/selected_devanagari_spec.spl
run_focused_spec test/01_unit/lib/skia/selected_arabic_spec.spl
run_focused_spec test/01_unit/lib/common/text_layout/font_renderer_spec.spl
run_focused_spec test/01_unit/lib/common/text_layout/font_render_config_spec.spl
run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl
run_focused_spec test/01_unit/lib/gpu/engine2d/font_runtime_config_spec.spl
run_focused_spec test/01_unit/lib/gpu/engine3d/font_compat_spec.spl
```

Lane D first executes its shared Engine2D prerequisite once:

```bash
run_focused_spec test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl
```

After that passes, Lane D executes the independent producer rows once each.
The Web row receives a nonempty immutable run ID. The x86 and RV64 specs run
their live wrappers internally, so no separate live-wrapper command precedes
them. Export the wrapper inputs so those child processes use the admitted CLI
and exact retained artifacts:

```bash
run_focused_spec test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_result_spec.spl
run_focused_spec test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl
run_focused_spec test/02_integration/rendering/wm_nested_content_frame_spec.spl
run_focused_spec test/01_unit/os/compositor/simple_web_window_renderer_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl
export SIMPLE_WEB_FONT_RUN_ID="font-${CHECKPOINT_SHA}-${CLI_SHA}"
export AETHERIC_HOST_WEB_GUI_SIMPLE_BIN="$CLI"
WEB_ATTEMPT=${WEB_ATTEMPT:-1}
case "$WEB_ATTEMPT" in
  1|2|3) ;;
  *) echo "WEB_ATTEMPT must be 1, 2, or 3" >&2; exit 2 ;;
esac
export AETHERIC_HOST_WEB_GUI_PROOF="$PWD/build/test-artifacts/shared_multilingual_gpu_fonts/web/attempt-$WEB_ATTEMPT/aetheric-host-web-gui.env"
test -f "$AETHERIC_HOST_WEB_GUI_PROOF"
run_focused_spec test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl
run_focused_spec test/03_system/gui/feature/gui_font_event_surface_spec.spl
run_focused_spec test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl
# Generate the hosted live bundle once with the capability-row command above;
# this focused spec consumes and validates that retained bundle.
run_focused_spec test/03_system/gui/linux_hosted_wm_live_window_spec.spl
export SIMPLE_BIN="$CLI"
run_focused_spec test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl
run_focused_spec test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl
export BUILD_DIR=build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live
export REPORT_PATH="$BUILD_DIR/report.md"
export RV64_DISPLAY_SMOKE_ELF=build/os/simpleos_riscv64_display_smoke.elf
export RV64_WM_FONT_DISK=build/os/fat32-riscv64-desktop.img
export RV64_WM_FONT_REGION_EXPECTED_SHA256="<reviewed-rv64-crop-sha256>"
run_focused_spec test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl
```

Lane E executes its five source contracts after runtime admission, then its
four hardware rows on a real graphics device:

```bash
export SIMPLE_BIN="$CLI"
export BUILD_DIR="$FOCUSED_ROOT/attempt-$FOCUSED_ATTEMPT"
run_focused_spec test/01_unit/helpers/shared_multilingual_gpu_fonts_perf_evidence_spec.spl
run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl
run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_font_scalar_receipt_spec.spl
run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_device_metadata_spec.spl
run_focused_spec test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl
run_focused_spec test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl
```

The perf run precedes native readback because native promotion consumes the
same attempt's sealed perf record. Both specs refuse to overwrite their typed
records. The aggregate path requires and hashes the perf measurement-started
record, passing perf record, and native readback record from this attempt root.
NFR-007 cannot currently be promoted: the
perf spec reports unavailable and the `set -e` runbook stops before native
readback. If invoked directly with complete focused evidence, the aggregate exits
with `font-owner-device-loss-runtime-proof-unavailable`; it validates the
focused native runner and trace directly rather than trusting a second summary
envelope. Source owners now retain scalar codes for
corrupt asset/program, unsupported format, compile/submit failure, and device
loss, plus identity and committed CPU-fallback state. Promotion still needs an
admitted current pure-Simple execution on one stable-identity hardware Vulkan
device; the source-fixed Vulkan3D fence-wait/wait-idle propagation still needs
that runtime receipt.
CPU, virtual, and software Vulkan devices are not promotion candidates. The AA
fields are named `*_limit`; they state the selected contract and are not
measured deltas.

The authoritative command graph contains 48 unique focused executions: one
runner preflight, 6 in B, 19 in C, 13 in D including its Engine2D prerequisite,
hosted focus contract, and SimpleOS artifact-root contract, and 9 in E. No path appears in more than
one group.

Each of the 44 docgen commands must exit zero and report the affected spec
complete with `0 stubs`. The owner retains the immutable identity, command,
both streams, exit, and manual hash; lane F reviews the generated operator
flow.

The separate prerequisite loop above must also exit zero and produce five
current `0 stubs` manuals. This does not change the 48-command focused graph or
the 44-font-manual count.

## Final gates owned by `/root`

```bash
set -euo pipefail
[ -z "$(find doc/06_spec -name '*_spec.spl' -print -quit)" ]
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
sh scripts/audit/numbered-artifact-guard.shs --working
sh scripts/audit/numbered-artifact-guard.shs --staged
git diff --check
"$CLI" check src/compiler
"$CLI" check src/lib
"$CLI" check src/app/mcp
"$CLI" check src/app/simple_lsp_mcp
SIMPLE_LIB=src "$CLI" test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
bash scripts/check/check-shared-multilingual-font-evidence.shs
prereq_root="build/test-artifacts/shared_multilingual_gpu_fonts/compiler-perf-prerequisite-docgen/attempt-${DOCGEN_ATTEMPT:?}"
[ "$(git rev-parse HEAD)" = "${CHECKPOINT_SHA:?}" ]
[ "$(sha256sum "$CLI" | awk '{print $1}')" = "${CLI_SHA:?}" ]
[ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" = "${CORE_C_SHA:?}" ]
while IFS='|' read -r spec manual artifact; do
  artifact="$prereq_root/$artifact"
  spec_sha=$(sha256sum "$spec" | awk '{print $1}')
  manual_sha=$(sha256sum "$manual" | awk '{print $1}')
  test -f "$artifact.err"
  test "$(tr -d '\r\n' < "$artifact.exit")" = 0
  grep -Fqx 'DONE Generated 1 docs (1 complete, 0 stubs)' "$artifact.out"
  grep -Fx "checkpoint_sha=$CHECKPOINT_SHA" "$artifact.command"
  grep -Fx "checkpoint_clean=true" "$artifact.command"
  grep -Fx "attempt=$DOCGEN_ATTEMPT" "$artifact.command"
  grep -Fx "cli=$CLI" "$artifact.command"
  grep -Fx "cli_sha256=$CLI_SHA" "$artifact.command"
  grep -Fx "core_c_dir=$CORE_C_DIR" "$artifact.command"
  grep -Fx "core_c_sha256=$CORE_C_SHA" "$artifact.command"
  grep -Fx "spec=$spec" "$artifact.command"
  grep -Fx "spec_sha256=$spec_sha" "$artifact.command"
  grep -Fx "manual=$manual" "$artifact.command"
  grep -Fx "manual_sha256=$manual_sha" "$artifact.manual.sha256"
done <<'PREREQUISITES'
test/01_unit/app/cli/bootstrap_focused_native_build_spec.spl|doc/06_spec/01_unit/app/cli/bootstrap_focused_native_build_spec.md|01_unit_app_cli_bootstrap_focused_native_build_spec.spl
test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl|doc/06_spec/01_unit/compiler/driver/bootstrap_context_mir_source_spec.md|01_unit_compiler_driver_bootstrap_context_mir_source_spec.spl
test/01_unit/compiler/mir/option_variant_order_source_spec.spl|doc/06_spec/01_unit/compiler/mir/option_variant_order_source_spec.md|01_unit_compiler_mir_option_variant_order_source_spec.spl
test/01_unit/compiler/hir/resolve_import_symbols_spec.spl|doc/06_spec/01_unit/compiler/hir/resolve_import_symbols_spec.md|01_unit_compiler_hir_resolve_import_symbols_spec.spl
test/01_unit/compiler/hir/symbol_display_name_spec.spl|doc/06_spec/01_unit/compiler/hir/symbol_display_name_spec.md|01_unit_compiler_hir_symbol_display_name_spec.spl
PREREQUISITES
```

The first command must print nothing. The five pure-runtime compiler/lib/MCP/LSP
commands are mandatory because compiler and CLI source changed; Rust diagnostics
cannot replace them. After the canonical owner-fault producer blocker is
removed, the remaining shared-font checker path revalidates and hash-seals
exactly 48 focused artifact sets, 44 docgen/manual records, the essential-tools
admission, and the runner calibration, then verifies the new seal before
reporting PASS. The following loop independently gates the five
prerequisite manuals against current checkpoint, CLI, core-C, source, canonical
manual, and recorded manual identities without changing those counts.
Existing-seal mode is reserved for a later
independent audit and must not be invoked immediately as a redundant rerun.
Final verification remains `STATUS: FAIL`
until every blocked row has authoritative evidence; unavailable hardware stays
a blocker rather than a synthetic or static PASS.

## 2026-07-27 final compiler-enablement cycle

The minimal native-arena fix and its two regressions passed independent static
review with no P0/P1 finding. The final allowed retained-Stage3 generation
cycle exported `SIMPLE_NATIVE_ARENA_DECLS=1`, eliminating the earlier NUL
environment panic. It then stopped with exit 132 at RIP `0x88034b`, the
`_format_hir_lowering_error+0x7b` nil trap: the obsolete `rt_for_iterable`
collector passed a nonnil `LoweringError` whose `span` was nil before
`err.span.file`. This is distinct from the earlier full-CLI MethodResolver trap
at RIP `0x559924`; the current typed indexed collector was absent from the
executing Stage3 producer. Its private cache still contains 675 objects and no
candidate ELF was created. Evidence is retained at
`/tmp/simple-cli-admission-20260727-6.isfZoU/build/mini_builds/minimal_repaired_compiler_final_fb09.log`
(SHA-256
`5cd89facfb881ee5a5f5003941e9bdf486f87b90dc0fe36573ec6e7482b5e034`).
The hard three-cycle cap prevents another build in this verification window;
the 39 focused runs, 34 docgens, and essential-tools smoke remain blocked.
The only authoritative resume contract is a future fresh window that first
proves an immutable pure-Simple parent/current source receipt, then uses the
cheapest adequate incremental build. The older Rust-seed, bridge, and cache
imperatives above are retained as history only.

## 2026-07-28 latest incremental profile

The branch was incrementally rebuilt on `origin/main` base `958db10638d`.
Pure-Simple Stage3 passed with 45 compiled, 647 cached, zero failed in 194.9s;
binary SHA-256:
`a920123d919c4a4c384161e16fe35a1853d6e3da6bfd3a4a4e7291a2c072f04d`.
The third and final Stage4 cycle found 1,340 unique sources and reached 50 HIR
modules by 15m38s. The local-symbol retention fix reduced observed RSS from
about 21.7 GiB in the prior run to about 7.0 GiB, but eager package-sibling
registration remained non-convergent. No full CLI, essential-tools smoke,
focused font execution, or docgen result exists. Retained log:
`build/native_probe/rebased-stage4-cycle3-final.log` (SHA-256
`92efd6d06e9c5e27ad45e98f472a953873bc78943bed43e2cb3e5855f2656fea`).
Afterward the source branch was completion-time rebased onto newer
`origin/main` base `9c19489a6e6`; no fourth build is permitted.
The remaining compiler performance blocker is tracked in
`doc/08_tracking/bug/stage4_low_memory_rss_growth_2026-07-18.md`.

## 2026-07-28 lazy package-sibling repair

The profiled eager package-sibling path now records only direct module keys and
registers a sibling declaration on its first real symbol/type/pattern/impl
lookup miss, at module scope. This removes package-wide declaration and method
lowering from every file while preserving the existing import/re-export owner.
The regression requires `Box` and `answer` to resolve but `unused` to remain
absent, which the old eager path cannot satisfy.

A pure-Simple incremental source build completed 693 files with zero failures
in 647.3s and produced SHA-256
`16f89715874448595f91a6a39043222c1967e320e9b73a9d519e61db4ab2c4c4`.
The linked producer contained 43 unresolved compatibility stubs and crashed on
a second native-build invocation. Per the existing three-cycle cap, no new full
Stage4 run was started. Resource, essential-tools, and font evidence therefore
remain open and `STATUS: FAIL` is unchanged.

The follow-up root-cause repair removes the remaining per-module full registry
scan: the driver now builds one package-to-direct-module index per lowering
invocation, and each lowerer selects its package slice directly while retaining
lazy symbol registration. The Stage 3 positional pure-Simple route also now
honors and restores `--runtime-path`, `--target`, `--cache-dir`, and `--threads`;
its canonical wrapper no longer selects Rust native-build and binds the admitted
native-all runtime explicitly. Independent review found no P0/P1 defect in
these changes.

The third and final producer attempt used the retained admitted pure-Simple
compiler, `SIMPLE_NO_STUB_FALLBACK=1`, the isolated shared cache, a two-thread
cap, the explicit host target, and the frozen Stage 2 runtime authority. The
old executing compiler remained CPU-active but emitted no phase result and no
candidate after 17m29s; it was stopped at the documented resource ceiling to
avoid another runaway. `/usr/bin/time -v` recorded maximum RSS 23,943,204 KiB.
Evidence is retained at
`build/native_probe/lazy-sibling-stage3-cycle3-pure/build.log`; the output is
absent. No fourth producer or full Stage4 build is permitted in this window.
The new index is present only in the not-yet-produced candidate, so this old
producer's memory profile is not performance evidence for or against it.

`STATUS: FAIL`

## 2026-07-28 compiler performance repair

Focused/incremental builds are now the default; a full bootstrap is required
only when changed seed/runtime inputs make it essential. Bounded inventory
found no eligible current CLI, parent, or provenance-valid reusable cache, and
the producer cap forbids a fourth attempt in this window.

Three shared hot-path defects are source-fixed: focused Stage4 now forwards and
exactly restores low-memory state; lowering builds one direct package-sibling
owner index per pass while retaining the legacy re-export fallback; and
module-qualified function access uses a direct index instead of materializing
all symbol keys per access. Independent focused, combined, and static reviews
passed.

Rust-seed diagnostics are not acceptance evidence. The qualified-function
spec passed; the low-memory and sibling-index specs stopped before examples on
the retained seed parser error in `module_lowering.spl` (`expected Comma, found
FString([Literal("}")])`). No new full CLI, essential-tools admission,
pure-Simple acceptance result, measured performance gain, focused font result,
or docgen exists. No fourth producer is permitted.

`STATUS: FAIL`
