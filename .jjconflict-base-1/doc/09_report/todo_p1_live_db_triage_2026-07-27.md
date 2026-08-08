# Live TODO DB — Open P1 Triage (2026-07-27)

Source of truth: `doc/08_tracking/todo/todo_db.sdn` (593 raw rows, regenerated
today). Canonicalization: drop `NN.` tier segments from paths, fold
`src/std/` -> `src/lib/`, dedupe on (canonical path, line, description).
Result: **554 unique rows, 51 open P1, 25 open P2**. `doc/TODO.md` is 20 days
stale and was not used.

Every classification below was made after reading the cited source. Read-only
triage: no builds were run, no source was edited.

---

## Structural findings (read these first)

1. **None of the 51 P1 rows corresponds to an inline `TODO`/`FIXME` comment at
   its cited `file:line`.** These are hand-authored ledger entries (the
   descriptions appear *only* in `todo_db.sdn` — `grep` for the id=580 text
   across the tree returns that one file). The `file`/`line` columns are
   attribution hints and are frequently wrong. Examples:
   - id=580 -> `src/app/io/_CliCompile/compile_targets.spl:633` is `di = di + 1`.
   - id=536 -> `src/compiler/backend/backend/llvm_native_link.spl:362` is a
     string literal `stage_dir + "/compiler_backfill_local.o"`.
   - id=559 -> `src/compiler/mir/_MirLoweringExpr/method_calls_literals.spl:508`
     is a blank line.
   - id=561 -> `src/compiler/frontend/core/tokens.spl:519` is
     `if kind == TOK_PERCENT: return true` inside `tok_is_multiplicative`.
   Do not use these line numbers for navigation.

2. **Two rows cite lines past EOF**: id=544 -> `src/app/simpleos_gpu_host/main.spl:59`
   (file is 8 lines); id=585 -> `src/compiler_rust/compiler/src/pipeline/native_project/config.rs:3159`
   (file is 439 lines).

3. **Three rows cite directories, not files**: id=540 -> `src/compiler/backend`,
   id=594 -> `src/compiler/mir`, id=593 -> `test/03_system`.

4. **6 of the 51 rows are the same issue.** ids 6, 96, 155, 355, 418, 487 carry
   byte-identical descriptions against six mirror copies of `signature_sffi.spl`
   (`src/lib/nogc_sync_mut/io/`, plus five test-tree copies under
   `test/01_unit/compiler/std/`, `test/01_unit/lib/database/lib/`,
   `test/feature/lib/lib/`, `test/unit/compiler/std/`,
   `test/unit/lib/database/lib/`). All 307 lines. **51 rows = 46 distinct issues.**

### Counts

| Classification | Count |
|---|---|
| DONE-ALREADY (source complete; only external verification outstanding) | 7 |
| ACTIONABLE-NOW | 15 |
| BLOCKED | 22 |
| STALE/UNCLEAR | 2 |
| DUPLICATE (of id=6) | 5 |
| **Total** | **51** |

---

## Triage table

Size: S = small (<1h), M = medium (a day), L = large (multi-day).

| id | cited file:line | verbatim description (truncated) | classification | size | blocker | subsystem |
|---|---|---|---|---|---|---|
| 119 | `doc/03_plan/agent_tasks/mac_gpu_backend_evidence_2026-07-10.md:1` | "Finish macOS self-host deployment and GPU queue runtime verification; require reviewer approval before closing" | BLOCKED | L | No macOS host on this machine; doc itself says "Reviewer decision: FAIL to close TODO 119" at :33 and "Obtain higher-model review" at :59 | gpu/macos |
| 530 | `doc/03_plan/compiler/bootstrap/cross_platform_dynload_remaining_plan_2026-07-10.md:14` | "Run one fresh canonical FreeBSD full bootstrap and retrieve the Stage 3 dynload artifact after the bounded-cycle fixes." | BLOCKED | M | FreeBSD CI runs 30181936568/30183860271 failed pre-artifact; bounded cycle exhausted. Doc:104 says close only after native-host gates pass | bootstrap/CI |
| 531 | same doc `:24` | "Run native macOS dynload and explicit full-CLI bootstrap verification on available Intel and Apple Silicon hosts." | BLOCKED | M | Missing hardware (Intel + Apple Silicon macOS) | bootstrap/CI |
| 532 | same doc `:36` | "Run native Windows MSVC and MinGW/UCRT Cranelift dynload and explicit full-CLI bootstrap verification." | BLOCKED | M | Missing Windows host; CI run 30183860262 died on a Git-Bash vendor path | bootstrap/CI |
| 533 | same doc `:48` | "Prove that the production launcher consumes refreshed pure-Simple dynload modules without replacing or relinking the monolithic CLI." | BLOCKED | M | CI run 30152376592 failed before the production-consumer gate | bootstrap/CI |
| 566 | `examples/09_embedded/simple_os/arch/common/host_gpu_ivshmem_probe_entry.spl:46` | "Measure and enforce guest-observed capability negotiation and fallback selection within 500 ms from device initialization…" | DONE-ALREADY | — | Budget constant exists: `SIMPLEOS_HOST_GPU_NEGOTIATION_BUDGET_US: i64 = 500000` at `src/lib/common/gpu/simpleos_host_gpu_protocol.spl:6`; per-arch probe entries at `host_gpu_ivshmem_probe_entry.spl:40-52`. Only fresh native proof (TODO 548) remains | simpleos/gpu |
| 578 | `examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c:1` | "Provide one duplicate-free x86 minimal freestanding runtime owner for the host-GPU probe without relying on linker multiple-definition ordering." | ACTIONABLE-NOW | M | none — `rt_extras.c` is 4478 lines and still defines `rt_tuple_new`/`rt_rdrand` (3 hits) alongside `baremetal_stubs.c`. NB: no `-z muldefs` occurrence found in tracked `scripts/**` or `src/**`, so that half of the note is unverifiable | simpleos/x86 boot |
| 564 | `scripts/check/check-cuda-generated-2d-readback.shs:1` | "Capture fresh multi-GPU and MIG-aware CUDA UUID identity evidence plus SimpleOS QEMU ProcessingIR receipts on a prepared NVIDIA host." | BLOCKED | M | Prepared MIG-capable NVIDIA host unavailable. Gate script is 2778/1207 lines and already fail-closed | gpu/cuda |
| 575 | `scripts/check/check-simpleos-qemu-guest-gpu-passthrough.shs:1` | "Prove or reject direct SimpleOS guest Vulkan/CUDA access through QEMU passthrough independently of the ivshmem host-daemon offload path." | BLOCKED | L | Both GPUs host-bound; `virtio-gpu-gl` unresolved `qemu_egl_display`; no SimpleOS guest Vulkan/CUDA producer exists | simpleos/gpu |
| 563 | `scripts/check/check-simpleos-qemu-host-gpu-2d.shs:1` | "Capture QEMU max RSS and warm multi-sample render/readback latency so NFR-003 and NFR-005 use measured p95 and combined QEMU-plus-daemon memory…" | BLOCKED | M | Needs fresh native/TCG execution on a supported host; machine load ~60 forbids | simpleos/gpu |
| 569 | same script `:1` | "Run the selected exact 1280x720 ARGB canonical render/readback fixture on every supported native host row and reject any pixel mismatch." | BLOCKED | M | TODO 548 (bounded rebuilds) + supported-host availability | simpleos/gpu |
| 535 | `src/app/cli/main.spl:1` | "Compose an exact-entry Stage 4 full-CLI host-provider profile from ABI-disjoint component archives without reopening hosted runtime bundles for applications." | BLOCKED | L | Stage-4 not green (`doc/09_report/stage4_campaign_summary_2026-07-27.md`); wrapper stopped at 5.8 GiB RSS. Cited file is an 18-line entry shim | bootstrap/stage4 |
| 580 | `src/app/io/_CliCompile/compile_targets.spl:633` | "Deploy a source-matched pure-Simple CLI, then unblock fresh CUDA, Vulkan, and Metal evidence." | BLOCKED | L | Native `CompileMode` aggregate-transport corruption before phase dispatch; three-cycle cap reached. Declared the critical WM->GUI/Web->DrawIR->Engine2D lane | bootstrap/gpu |
| 586 | `src/app/simpleos_gpu_host/daemon_runner.spl:292` | "Measure the source-matched ProcessingIR production daemon after removing duplicate CPU work." | BLOCKED | M | Source half is done — `daemon_runner.spl:288-297` gates the CPU mirror behind `if processing_verify_cpu:` and goes straight to `platform.execute_processing`. Measurement needs an admitted compiler (TODO 585/580) | gpu/daemon |
| 577 | `src/app/simpleos_gpu_host/main.spl:1` | "Make the linked native host-GPU daemon enter the ivshmem service loop and advance HELLO generation before guest negotiation." | BLOCKED | M | Needs a native build + AArch64 QEMU run (TODO 548); cited `main.spl` is an 8-line entry shim, real logic is `daemon_runner.spl` (510 lines) | simpleos/gpu |
| 544 | `src/app/simpleos_gpu_host/main.spl:59` (past EOF) | "Implement and verify native Metal/DirectX/CUDA host executors beneath DrawIR/ProcessingIR for the remaining SimpleOS QEMU host rows." | BLOCKED | L | Missing hardware (Windows DirectX host, prepared macOS Metal host); CUDA row already passes | gpu |
| 540 | `src/compiler/backend` (directory) | "Filter target-gated duplicate global values before native symbol resolution, matching cfg function selection." | ACTIONABLE-NOW | M | none — no cfg-aware global filter found under `src/compiler/70.backend/`; symptom is an AArch64 PCI build selecting the later `riscv64` cfg ECAM global | compiler/backend |
| 536 | `src/compiler/backend/backend/llvm_native_link.spl:362` | "Keep focused multiarch entries inside their source root and harden LLD defsym only if correctly rooted modules still contain expression punctuation." | ACTIONABLE-NOW | S-M | none — the placeholder hack is live at `src/compiler/70.backend/backend/llvm_native_link.spl:2371-2374` (`--defsym=unknown_0=rt_riscv_uart_put` … `unknown_3=rt_riscv_qemu_ram_base`) | compiler/backend |
| 537 | same file `:473` | "Fix deployed RV freestanding-runtime object selection and SBI unsafe/inline-asm lowering without local runtime shims." | ACTIONABLE-NOW | M | none for the source half — `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` (4352 lines) now owns `rt_for_iterable`, `rt_function_not_found`, `rt_byte_array_new`, but has **zero** definitions of `rt_array_push_i64`, `rt_time_now_nanos`, `rt_memory_barrier`. Link proof then needs TODO 548 | simpleos/riscv |
| 579 | `src/compiler/frontend/core/parser.spl:1` | "Verify labeled tuple return parsing and the honest Stage3 SMF compile command in a fresh bounded bootstrap cycle." | DONE-ALREADY | — | Source-side fix landed (`parser.spl`, 907 lines, parses `label: Type` tuple elements). Remaining item is literally "verify in a fresh bounded bootstrap cycle" — blocked by Stage-4/build load | compiler/parser |
| 561 | `src/compiler/frontend/core/tokens.spl:519` | "Allow a binary operator at end of line to continue its right-hand expression at the current indentation level in the pure-Simple parser." | DONE-ALREADY | — | `token_requires_rhs` implemented at `src/compiler/10.frontend/core/tokens.spl:525-535`, exported `:575`, consumed by `lexer_struct.spl:896,977` and `lexer_scanners.spl:453,493`; regression at `test/01_unit/compiler/parser/dedent_continuation_spec.spl`. Blocked only on pure-Simple deployment (canonical binary still identifies as the Rust seed) | compiler/lexer |
| 592 | `src/compiler/hir/hir_lowering/expressions.spl:330` | "Prove and repair generic module-namespace call lowering without undeclared globals." | DONE-ALREADY | — | Fix in place: `src/compiler/20.hir/hir_lowering/expressions.spl:355` carries the `# Dict.values() corrupts struct values` note and the keys()+bracket rewrite; durable gate exists at `test/03_system/compiler/native_module_namespace_call_regression_spec.spl`. Execution blocked on Stage-4 admission | compiler/hir |
| 594 | `src/compiler/mir` (directory) | "Pre-register every instrumented decision site so unexecuted branches remain in the coverage denominator." | ACTIONABLE-NOW | L | none, but large — `grep -rl 'DecisionProbe\|ConditionProbe' src/compiler src/lib` returns **nothing**; the probes exist only in the Rust seed (`src/compiler_rust/compiler/src/codegen/instr/coverage.rs`). Pure-Simple MIR must emit them first | coverage |
| 559 | `src/compiler/mir/_MirLoweringExpr/method_calls_literals.spl:508` | "Preserve Optional not-found semantics when bootstrap MIR lowers rfind on an erased text receiver." | DONE-ALREADY | — | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1861-1990` contains the explicit `-1`-vs-`nil` handling, the `rt_string_rfind` mapping (`:1977`) and the tagged-handle note (`:1984`). Cited line 508 is blank | compiler/mir |
| 584 | `src/compiler/mir_opt/mir_opt/mod.spl:748` | "Repair native OptimizationPipeline aggregate transport before resuming the 84 oracle and Vulkan readback." | BLOCKED | M | The Simple source is well-formed (`optimizationpipeline_for_backend` at `:651`, `optimize_module_for_backend` at `:743`, call site at `:748`); the fault is a native-codegen aggregate-transport segfault. Three-cycle cap reached | compiler/mir_opt |
| 558 | `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:1` | "Preserve Result<T,E>.unwrap() payload types for unannotated local receiver method resolution and deduplicate raw/mangled aliases in ambiguity diagnostics." | ACTIONABLE-NOW | M | none — Rust-seed-local change; the temporary `CompiledModule` annotation named in the ledger is the thing to remove | compiler/rust-seed |
| 557 | `src/compiler_rust/compiler/src/hir/types/expressions.rs:114` | "Enforce lexical unsafe scope in the Rust seed so raw pointer, SFFI, and inline-assembly operations are rejected outside UnsafeBlock." | ACTIONABLE-NOW | M | none — `UnsafeBlock(Vec<HirStmt>)` exists at `expressions.rs:114` and is lowered at `hir/lower/expr/mod.rs:186`, but `grep -rn in_unsafe src/compiler_rust` returns **zero** hits. The pass to port is `src/compiler/35.semantics/safety_checker.spl:35,44,134-142` | compiler/rust-seed, safety |
| 585 | `src/compiler_rust/compiler/src/pipeline/native_project/config.rs:3159` (past EOF) | "Provide an admitted no-stub runtime lane for the pure-Simple compiler entry closure." | BLOCKED | L | Stage-4 not green; ledger says run only "when concurrent bootstrap load clears" — load is ~60 now | runtime/bootstrap |
| 562 | `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1243` | "Include resolved import/provider ownership and dependency source hashes in native object-cache invalidation." | ACTIONABLE-NOW | M | none — confirmed at `native_project/mod.rs:1346-1360`: `object_cache_key(content, is_entry, backend, no_mangle, module_prefix, opt_level)` hashes only those six; no dependency or provider inputs | compiler/cache |
| 560 | `src/compiler_rust/compiler_backfill/src/lib.rs:1` | "Replace the focused Stage4 compiler capsule's direct rt_cranelift ABI with a typed compiler-provider surface." | STALE/UNCLEAR | — | The named file is 15 lines containing only `mod shared { pub fn platform_call_conv() -> CallConv }`; `build.rs` is 3 lines; the crate has **zero** `rt_` references. The 73-hook capsule and `rt_cranelift_*` surface actually live in `src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs:302+`. Either re-point this row at that file or close it | compiler/rust-seed |
| 591 | `src/lib/common/compress/gzip.spl:22` | "Repair the pure-Simple fixed-Huffman gzip round trip before using it to admit dynamic Huffman return annotations." | ACTIONABLE-NOW | M | none — real code, interpreter-testable: `gzip.spl:21-27` (compress), `:29-48` (decompress, `header_size`/`footer_offset`/`inflate`), and `src/lib/nogc_sync_mut/compression/gzip/inflate.spl:356` `fn inflate(input: [u8]) -> [u8]?`. Specs exist at `test/01_unit/lib/common/compress/gzip_spec.spl` | compression |
| 549 | `src/lib/common/gpu/simpleos_host_gpu_draw_ir.spl:1` | "Finish production IMAGE offload after the bounded SimpleOS host-GPU resource wire." | BLOCKED | M | Source implemented (741 lines, fail-closed provenance); "fresh compiler/QEMU execution remains open" -> TODO 548 | simpleos/gpu |
| 552 | `src/lib/common/gpu/simpleos_host_gpu_protocol.spl:6` | "Expand the bounded SimpleOS host-GPU wire capacity for the 3840x2160 production desktop without downscale or crop." | ACTIONABLE-NOW | S-M | none — confirmed at `simpleos_host_gpu_protocol.spl:7`: `SIMPLEOS_HOST_GPU_REGION_BYTES: i64 = 8 * 1024 * 1024`, with `CONTROL_BYTES` 4 KiB (`:8`) and `MAX_PAYLOAD_BYTES` 64 KiB (`:9`). 4K ARGB needs 33,177,600 bytes | simpleos/gpu |
| 550 | `src/lib/gc_async_mut/processing/vulkan_fill_u32.spl:75` | "Expose stable selected-device identity in every ProcessingIR backend result instead of treating a transient resource handle as device identity." | DONE-ALREADY | — | `vulkan_fill_u32.spl:63-75`: every `ProcessingVulkanResult(...)` already carries `device_identity:` as a field distinct from `backend_handle:`. Only the Metal identity row (macOS host) is open | gpu |
| 590 | `src/lib/nogc_sync_mut/compression/gzip/huffman.spl:1` | "Annotate genuine value-returning functions that Stage 4 rejects as implicitly void, then rerun admission in a fresh bounded environment." | BLOCKED | L | Stage-4 not green; 70 of 97 physical declarations remain; the ledger forbids bulk annotation until TODO 591 (gzip round trip) is fixed | bootstrap/stage4 |
| 573 | `src/lib/nogc_sync_mut/io/process_ops.spl:1` | "Provide provider-complete timeout/capture, process-tree cleanup, child-scoped environment, and atomic unique-temp facades; remove POSIX env/mktemp admission dependencies." | ACTIONABLE-NOW | M | none. Two clauses are already STALE: core-C **does** have `rt_process_run_timeout` (`src/runtime/runtime_process.c:508,1461`) and Windows **does** have Job Object cleanup (`runtime_process.c:365,405,466,666,703,872`). Still real: `grep setpgid\|killpg runtime_process.c` = 0 hits (no Unix process-group); `process_ops.spl:174` still spawns `cmd /c`; `process_ops.spl:108` still reads `TMPDIR` for a hand-rolled temp file; no child-env overlay | runtime/process |
| 6 | `src/lib/nogc_sync_mut/io/signature_sffi.spl:129` | "Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding … Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl …" | STALE/UNCLEAR | — | The cited repro **does not exist**: `test/03_system/os_crypto_ref_signature_spec.spl` is absent. Cited line 129 is `fn rsa_sha256_sign(pkcs8: [u8], message: [u8]) -> [u8]:`, which calls `rt_rsa_sha256_sign` directly with no unwrap (`:141`). The `_unwrap_sig` workaround is still live but in a *different* file: `src/lib/common/crypto/ecdsa_p256.spl:9,32,49`. Ambiguous whether the marshalling defect still reproduces — needs a fresh repro before it can be actioned | interpreter/SFFI |
| 574 | `src/lib/nogc_sync_mut/io/time_ops.spl:49` | "Provide overflow-safe cross-platform monotonic millisecond conversion and split QEMU runner elapsed timing from wall-clock artifact stamps." | ACTIONABLE-NOW | S | none — **confirmed live bug**: `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:1748-1756` implements `rt_time_now_monotonic_ms` as `SystemTime::now().duration_since(UNIX_EPOCH).as_millis()` — wall clock, not monotonic. The QPC-overflow clause is already STALE: `src/runtime/runtime_time.c:31` divides before multiplying (`seconds * 1e9 + (remainder * 1e9)/frequency`). `time_ops.spl:44-60` docstrings still claim `CLOCK_MONOTONIC_RAW` | runtime/time |
| 572 | `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:54` | "Execute focused SSpec files through a result-bearing pure-Simple compiler/test-runner path without rt_cli_run_tests, the Rust rt_cli_run_file interpreter, SIMPLE_BOOTSTRAP_DRIVER, or a seed subprocess." | ACTIONABLE-NOW | L | none — confirmed: `rt_cli_run_tests` still declared/wrapped at `src/lib/nogc_sync_mut/sffi/cli.spl:114-117` and `ffi/cli.spl:114-117`; `rt_cli_run_file` at `test_runner_fork.spl:22`, `sffi/cli.spl:99`, `debug/interpreter_backend.spl:26,64`. `driver_api_interpret` **does not exist anywhere in the tree** — it must be written | test-runner |
| 548 | `src/os/_QemuRunner/os_build_run.spl:380` | "Make focused SimpleOS host-GPU guest rebuilds and checks bounded, crash-free, and cache-progress-visible under concurrent compiler load." | BLOCKED | M | Needs one final source-matched Stage2/3 admission run; machine load ~60. **This is the hub blocker for 566, 569, 549, 565, 568, 567, 544, 529** | bootstrap/simpleos |
| 565 | `src/os/compositor/engine2d_wm_frame_executor.spl:1` | "Complete AArch64 and RISC-V production desktops through the canonical SharedWmScene, Engine2D, and Engine2dWmFrameExecutor host-GPU path…" | BLOCKED | L | Source/spec present (294 lines); TODO 548 blocks fresh compiled/QEMU proof; TODO 567 owns pure-Simple DMA | simpleos/compositor |
| 568 | `src/os/kernel/arch/arm64/ramfb.spl:1` | "Move AArch64 RAMFB setup and UART input used by the canonical desktop from the legacy wm_entry_io demo into architecture-owned Simple facades…" | DONE-ALREADY | — | `ramfb.spl` (217 lines) is the arch-owned facade; ledger records `wm_entry_io` and direct `rt_*` removed from the canonical closure. Only the freestanding compile/QEMU proof (TODO 548) is open | simpleos/arm64 |
| 567 | `src/os/kernel/arch/riscv64/display.spl:1` | "Replace the transitional RISC-V C VirtIO transport with pure-Simple DMA/queue ownership while preserving the architecture display facade…" | ACTIONABLE-NOW | L | none for the implementation — `display.spl` is 44 lines and is **entirely** `extern fn rt_display_*` / `rt_riscv_noalloc_pmm_init_default`; no pure-Simple DMA or virtqueue code exists yet. Proof (not implementation) needs TODO 548 | simpleos/riscv |
| 96, 155, 355, 418, 487 | five mirror copies of `signature_sffi.spl:129` | (identical to id=6) | DUPLICATE | — | DB hygiene: one issue counted six times | interpreter/SFFI |
| 589 | `test/01_unit/lib/common/ui/host_env_contract_spec.spl:1` | "Measure and enforce 98-100% decision coverage for the owned WM/GUI/Web/Engine2D host-evidence contracts with an accepted pure-Simple runtime." | BLOCKED | M | Contract annotation is present (`host_env_contract_spec.spl:1` = `# @cover src/lib/common/ui/host_env_contract.spl 100%`), but the ledger explicitly gates this on TODO 572 + 580/585 delivering an accepted no-stub runtime | coverage |
| 593 | `test/03_system` (directory) | "Migrate canonical system specs that lack an explicit per-owner # @cover path N% contract." | ACTIONABLE-NOW | L | none technically — 977 of 3143 canonical specs unannotated, 55 with legacy non-percent forms. Per-owner review chore, explicitly must not be bulk-invented | coverage |
| 529 | `test/03_system/app/engine2d_in_qemu_spec.spl:57` | "Capture and commit an independently reviewed SimpleOS Engine2D QEMU PPM oracle, then run the pure-Simple QMP exact-pixel gate for x86_64, AArch64, and RV64." | BLOCKED | M | "independent QEMU oracle required" — needs a second reviewer plus three QEMU runs. Spec is real: `engine2d_in_qemu_spec.spl:48-57` builds the strict x86_64 guest then asserts a nonblank QMP frame | simpleos/engine2d |

---

## ACTIONABLE-NOW grouped by subsystem

**Compiler / Rust seed (4)** — same crate, batchable in one pass:
- id=557 port `in_unsafe` safety pass (`src/compiler/35.semantics/safety_checker.spl` -> `src/compiler_rust/compiler/src/hir/`)
- id=558 `Result<T,E>.unwrap()` payload typing (`hir/lower/expr/mod.rs`)
- id=562 object-cache key inputs (`pipeline/native_project/mod.rs:1346`)
- id=574 (Rust half) monotonic clock (`interpreter_extern/file_io.rs:1748`)

**Compiler / native backend + linking (3)**:
- id=540 cfg-gated duplicate global filtering (`src/compiler/70.backend/`)
- id=536 LLD `--defsym=unknown_N` hardening (`llvm_native_link.spl:2371-2374`)
- id=537 RV64 freestanding runtime symbol owners (`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`)

**Runtime / platform facades (2)**:
- id=573 Unix process-group + child-env overlay + host unique-temp (`src/runtime/runtime_process.c`, `src/lib/nogc_sync_mut/io/process_ops.spl`)
- id=574 (Simple half) split runner elapsed timing from wall-clock stamps (`src/lib/nogc_sync_mut/io/time_ops.spl`)

**SimpleOS / GPU wire (2)**:
- id=552 4K wire capacity (`simpleos_host_gpu_protocol.spl:6-12`)
- id=578 x86 freestanding runtime single-owner (`rt_extras.c` vs `baremetal_stubs.c`)

**SimpleOS / RISC-V (1)**:
- id=567 pure-Simple VirtIO DMA/queue (`src/os/kernel/arch/riscv64/display.spl`)

**Compression (1)**:
- id=591 gzip fixed-Huffman round trip (`src/lib/common/compress/gzip.spl`, `.../gzip/inflate.spl`)

**Test runner / coverage (3)** — sequentially dependent (572 -> 594 -> 593/589):
- id=572 result-bearing pure-Simple spec execution path
- id=594 decision-site pre-registration in pure-Simple MIR
- id=593 `@cover` contract migration for 977 system specs

---

## Ranked top 8 (value / effort)

**1. id=574 — monotonic clock is a wall clock (S).**
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:1748-1756` returns
`SystemTime::now().duration_since(UNIX_EPOCH)` from `rt_time_now_monotonic_ms`,
so every interpreter-mode elapsed measurement is NTP- and DST-sensitive. Replace
with a lazily-initialised `std::time::Instant` baseline (`OnceLock<Instant>`) and
return `start.elapsed().as_millis()`, matching the already-correct C owner at
`src/runtime/runtime_native.c:6511`. Then drop the stale QPC clause from the
ledger — `src/runtime/runtime_time.c:31` already divides before multiplying.

**2. id=591 — gzip round trip (M).**
`gzip_compress` (`src/lib/common/compress/gzip.spl:21-27`) produces bytes but
`gzip_decompress` (`:29-48`) returns empty. Bisect by calling
`src/lib/nogc_sync_mut/compression/gzip/inflate.spl:356 fn inflate` directly on the
compressed slice to separate raw inflate from `gzip_header_size`/`gzip_footer_validate`,
using the existing `test/01_unit/lib/common/compress/gzip_spec.spl` vectors. This
is interpreter-testable — it does **not** need Stage-4 — and it unblocks the
70-declaration annotation campaign in id=590.

**3. id=562 — object-cache key ignores dependencies (M).**
`object_cache_key` at `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1346`
hashes only `content, is_entry, backend, no_mangle, module_prefix, opt_level`. Add
the resolved import/provider set and each dependency's source hash to the hasher,
and populate the currently-empty `dependencies` in the pure-Simple `BuildCache`.
This is the defect that let a changed `daemon_runner` keep a stale flattened
`simpleos_gpu_host__main___process_request` object — i.e. it silently produces
wrong binaries, which poisons every other investigation.

**4. id=557 — unsafe scope unenforced in the Rust seed (M).**
`UnsafeBlock` survives to HIR (`hir/types/expressions.rs:114`, lowered at
`hir/lower/expr/mod.rs:186`) but `in_unsafe` appears nowhere in `src/compiler_rust`.
Port the pure compiler's pass verbatim — `src/compiler/35.semantics/safety_checker.spl:35`
(context field), `:44` (init), `:134-142` (enter/exit + the `if not self.context.in_unsafe`
rejection) — as a seed HIR visitor. Raw-pointer/SFFI/inline-asm outside `unsafe:`
is currently accepted by the seed, so this is a real safety hole, not a nicety.

**5. id=552 — 8 MiB wire cannot carry a 4K desktop (S-M).**
`src/lib/common/gpu/simpleos_host_gpu_protocol.spl:7` fixes the shared region at
8 MiB; after 4 KiB control (`:8`) and 64 KiB payload (`:9`) only 8,318,976 readback
bytes remain versus 33,177,600 for 3840x2160 ARGB. Either raise
`SIMPLEOS_HOST_GPU_REGION_BYTES` and the ivshmem size in the QEMU argv together, or
add a tiled readback protocol with a chunk index in the control block. Bump
`SIMPLEOS_HOST_GPU_PROTOCOL_VERSION` (`:5`) either way so old guests fail closed.

**6. id=536 — LLD `unknown_N` defsym hack (S-M).**
`src/compiler/70.backend/backend/llvm_native_link.spl:2371-2374` maps
`unknown_0..unknown_3` onto `rt_riscv_uart_put`, `_uart_put`,
`rt_riscv_qemu_reserved_end`, `rt_riscv_qemu_ram_base` — positional placeholders
that will silently mis-bind the moment symbol ordering changes. Root-cause why
those modules emit `unknown_N` (expression punctuation leaking into symbol names
for entries rooted outside their source root) and gate the defsym fallback on a
verified name match instead of position.

**7. id=537 — RV64 freestanding runtime symbol owners (M).**
`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` (4352 lines) already owns
`rt_for_iterable`, `rt_function_not_found` and `rt_byte_array_new`, but greps zero
for `rt_array_push_i64`, `rt_time_now_nanos`, and `rt_memory_barrier` — exactly the
tail of the reported link-failure set. Add those three owners next to the existing
ones and re-run only the RV64 probe link; x86_64 and AArch64 already build and boot.

**8. id=573 — Unix process-group cleanup missing (M).**
`grep setpgid\|killpg src/runtime/runtime_process.c` = 0 hits, so a timed-out child's
descendants are orphaned on Unix — while Windows already has full Job Object cleanup
(`runtime_process.c:365,405,466,666,703,872`). Add `setpgid(0,0)` in the forked child
and `killpg` on the timeout path, then replace the `cmd /c` shell hop at
`src/lib/nogc_sync_mut/io/process_ops.spl:174` and the `TMPDIR` hand-rolled temp file
at `:108` with provider calls. Trim the two stale clauses (core-C `rt_process_run_timeout`
exists at `runtime_process.c:508`; Job Objects exist) from the ledger entry.

---

## Mis-prioritized items

**Should be P0 (or at least flagged as the critical path):**
- **id=548** — it is the single hub blocking eight other open P1 rows (566, 569,
  549, 565, 568, 567, 544, 529). Everything in the SimpleOS/GPU lane is waiting
  on one bounded Stage2/3 admission run. Raising it to P0 would make the
  dependency visible; today it reads as a peer of the rows it blocks.
- **id=574** — a monotonic clock that is actually a wall clock
  (`file_io.rs:1748`) silently corrupts every latency median the project uses as
  gate evidence (see id=586's "medians remain historical only"). A correctness
  defect that invalidates measurements outranks the evidence-capture chores it
  currently sits beside.

**Over-prioritized / should not be P1:**
- **id=560** — P1, but the file it names
  (`src/compiler_rust/compiler_backfill/src/lib.rs`) is a 15-line stub with a
  3-line `build.rs` and zero `rt_` references. The described capsule is not
  there. Close it or re-point it at
  `src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs:302+`; it cannot be
  worked as written.
- **id=6** — P1 whose entire repro (`test/03_system/os_crypto_ref_signature_spec.spl`,
  "17 failing tests") no longer exists, and whose cited line
  (`signature_sffi.spl:129`) is an unrelated `rsa_sha256_sign` wrapper. Demote
  until someone reproduces it; the live artifact is the `_unwrap_sig` workaround
  in a different file (`src/lib/common/crypto/ecdsa_p256.spl:32`).
- **id=593** — "migrate 977 specs to `@cover` annotations" is a documentation /
  hygiene chore with no defect behind it, and it is explicitly gated on per-owner
  review that cannot be bulk-applied. P2 at most.
- **ids 96, 155, 355, 418, 487** — five duplicate rows for id=6, caused by five
  mirror copies of `signature_sffi.spl` living under `test/`. They inflate the
  open-P1 count by ~10% for zero distinct work. Fix the scanner's mirror handling
  or delete the stale test-tree copies.

**Structurally mis-filed (not a priority issue, but blocks triage):**
- **ids 530-533, 531, 532, 119, 564, 575** are all hardware/CI evidence-capture
  chores (FreeBSD, Intel + Apple Silicon macOS, Windows MSVC/MinGW, MIG-capable
  NVIDIA, VFIO passthrough). None can ever clear on this host. They are seven of
  the 51 P1 rows and would be better tracked in a separate "awaiting hardware"
  queue than mixed with actionable defects.
- **ids 540, 594, 593** cite *directories* rather than files, and **ids 544, 585**
  cite lines past EOF. Since no P1 row has a real inline `TODO` marker at its
  cited location, the `file`/`line` columns for hand-authored ledger rows should
  either be validated at insert time or dropped.

---

## Follow-up session 2026-07-28 — re-verification and landed work

Scope: the ACTIONABLE-NOW set minus the five items owned by parallel sessions
(574 monotonic clock, 562 object-cache key, 557 unsafe enforcement, 591 gzip
round trip, ALPN/QUIC). Each row below was re-checked against current source
before any edit.

### Completed

**id=537 — RV64 freestanding runtime symbol owners: source half DONE.**
`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` now defines the two
symbols that were genuinely missing:
- `rt_memory_barrier` -> `fence rw,rw` (RISC-V peer of the arm64 owner's
  `dsb sy` in `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`).
  Referenced by `src/os/kernel/boot/mmio_hardware.spl:11`,
  `src/os/drivers/virtio/virtio_gpu.spl:76`, `src/lib/nogc_sync_mut/io/volatile_ops.spl:58`.
- `rt_time_now_nanos` -> `rdtime * 100` (QEMU virt / FPGA CLINT timebase is
  10 MHz, `src/os/kernel/arch/riscv64/timer.spl:29 TIMER_FREQ_HZ`), placed next
  to the pre-existing `rt_time_now_unix_micros` owner which reads the same CSR.
  Referenced by `src/lib/nogc_sync_mut/io/time_ops.spl:8` and
  `src/lib/common/time_utils.spl:188`.

Verified: `riscv64-unknown-elf-gcc -march=rv64gc -mabi=lp64d -mcmodel=medany
-ffreestanding -nostdlib -DSIMPLE_BOOT_MINIMAL=1 -DSIMPLE_RUNTIME_NO_ENTRY=1
-DSIMPLE_RUNTIME_NO_WEAK_HEAP=1 -c` (the exact flag set from
`src/compiler/70.backend/backend/llvm_native_link.spl:2333-2337`) compiles clean,
and `riscv64-unknown-elf-nm` shows both as strong `T` definitions. Link proof
still needs TODO 548.

**Ledger correction for id=537:** the third named symbol, `rt_array_push_i64`,
**does not exist anywhere in the owned tree** (`grep -rn 'rt_array_push_i64\b'`
over `src/ examples/ test/` minus vendor = 0 hits). The real runtime symbol is
`rt_array_push_i64_raw` (`src/runtime/runtime.h:370`,
`src/runtime/runtime_native.c:3846`) and it is not referenced from any RV64
Simple source. Nothing to add; drop that clause instead of writing dead code.

### Re-verified as NOT actionable / ledger stale

**id=573 — the process-tree clause is STALE, not open.** The triage's
`grep setpgid|killpg src/runtime/runtime_process.c = 0 hits` was scoped to the
wrong file. Unix process-group cleanup is fully implemented:
- `src/runtime/runtime_fork.c:212` `setpgid(0,0)` in the forked child,
  `:237` `setpgid(pid,pid)` race-close in the parent,
  `:276` and `:428` `kill(-pid, SIGKILL)` group kill on timeout / forced cleanup.
- `src/runtime/runtime_process.c:1289` `setpgid(0,0)`, `:1335` parent `setpgid`,
  `:1182` `posix_spawnattr_setpgroup`, `:1028` `kill(-pid, signal)`.
Combined with the two clauses the original triage already found stale
(core-C `rt_process_run_timeout` exists; Windows Job Objects exist), **three of
id=573's four clauses are done.** What actually remains is smaller than the row
implies and is written up below.

### Written up instead of implemented

**id=552 — 4K host-GPU wire capacity. Needs an architecture decision; do not
bump the constant alone.** Arithmetic confirmed: 3840x2160 ARGB = 33,177,600 B;
usable readback today is `8 MiB - 4 KiB control - 64 KiB payload` = 8,318,976 B
(`src/lib/common/gpu/simpleos_host_gpu_protocol.spl:7-9,19-21`). ivshmem BAR2 is
power-of-two sized, so the next viable region is **64 MiB**, not 33 MB. The
blocker is that 8 MiB is hard-coded in the *guest memory map*, not just the
constant:
- `src/os/kernel/ipc/host_gpu_ivshmem_map.spl:45` rejects any BAR2 whose probed
  size `!= 0x00800000`.
- `:22` (arm64) requires exactly `base == 0x3E000000 and size == 0x00800000`.
  On QEMU `virt` the 32-bit PCIe MMIO window ends at `0x3EFF0000` and RAM starts
  at `0x40000000`, so **64 MiB does not fit there** — aarch64 would have to move
  to the high MMIO window (`0x8000000000`).
- `:6` (x86_64) and `:14` (riscv64) stride devices by `0x01000000` (16 MiB), which
  a 64 MiB region overruns; both strides must widen.
- `src/os/kernel/arch/x86_64/host_gpu_ivshmem_vmm.spl:11` identity-maps the whole
  region a 4 KiB page at a time — 2,048 -> 16,384 mappings.
- Host side: `size=8M` appears ~10x plus `truncate -s 8388608` in
  `scripts/check/check-simpleos-qemu-host-gpu-2d.shs` (`:701,1014,1431-1452`).
Either path (raise region + relocate the aarch64 window, or add a tiled readback
with a chunk index in the control block) changes the guest physical memory map
and must bump `SIMPLEOS_HOST_GPU_PROTOCOL_VERSION` (`:5`) so old guests fail
closed. Neither can be proven here — validation needs the QEMU runs blocked by
TODO 548. **Recommend re-scoping id=552 as a design task, not a constant bump.**

**id=578 — x86 duplicate freestanding owners: exact duplicate set measured, but
not safely fixable without a boot proof.** Both files are in the same x86_64
link (`src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl:155`
`baremetal_stubs.c` in `boot_c_sources`, `:171` `rt_extras.c` in
`grandfathered_native_sources`). 14 `rt_*` symbols are strongly defined in both
`baremetal_stubs.c` and `rt_extras.c`:
`rt_array_new`, `rt_bytes_alloc_packed`, `rt_bytes_alloc_packed_empty`,
`rt_char_from_code`, `rt_native_eq`, `rt_rdrand`, `rt_string_from_cstr`,
`rt_string_len`, `rt_tuple_get`, `rt_tuple_len`, `rt_tuple_new`, `rt_tuple_set`,
`rt_typed_words_u32_at`, `rt_value_float`.
`rt_rdrand` additionally has **mismatched signatures** between the two owners
(`RuntimeValue rt_rdrand(void)` at `rt_extras.c:1159` vs
`int64_t rt_rdrand(void)` at `baremetal_stubs.c:7395`), and `auto_stubs.c` adds a
third, weak, nil-returning 8-arg variant for both — the exact "WEAK nil-returning
`rt_*` stub" family that has already produced silent empty-aggregate faults in
the guest. Picking a winner per symbol is a 14-way judgement call whose only
honest proof is an x86_64 build + boot, which TODO 548 blocks. Note
`doc/07_guide/platform/simpleos/qemu_system_tests.md:747` already records the
intended direction ("reject the diagnostic that admitted all of `rt_extras.c`").
Leave open; do not dedupe blind.

**id=573 residual — atomic unique temp + child-env overlay needs a new runtime
primitive.** `src/lib/nogc_sync_mut/io/process_ops.spl:105-113` builds
`/tmp/simple_out_{pid}_{micros}.txt` by string interpolation: predictable name in
a world-writable directory (symlink-follow on the redirect) and collision-prone
across containers sharing a PID namespace. `:174` still shells through `cmd /c`
on Windows, and there is no child-scoped environment overlay. The clean fix needs
an `O_EXCL`/`mkdtemp`-backed primitive exposed as a facade — no such primitive
exists today (`grep mkstemp|mkdtemp src/runtime` = 0; the only `O_EXCL` uses are
`runtime.c:1484` and `runtime_native.c:5919,5924`, both private to atomic file
writes). That is core-C + SFFI + facade + Windows work, so it is a real task, not
a small fix. Keep id=573 open but re-scope its description to the residual.

### Left for others (unchanged, still large or blocked)

id=536 (LLD `--defsym=unknown_N`, `llvm_native_link.spl:2371-2383` — 13 positional
placeholders; hardening requires root-causing why the modules emit `unknown_N` at
all, plus an `nm`-based name check, and an RV64 link to prove it),
id=540, id=558, id=567, id=572, id=593, id=594 — all confirmed large or
investigation-shaped, unchanged from the original triage.
