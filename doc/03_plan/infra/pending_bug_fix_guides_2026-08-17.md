# Pending bug fix guides + hardware requirements — 2026-08-17

Scope: every doc under `doc/08_tracking/bug/` dated `2026-08-1*` carrying no
closure marker (RESOLVED / FIX LANDED / NOT A BUG / CLOSED / WONTFIX / FIXED).

```sh
for f in doc/08_tracking/bug/*2026-08-1*.md; do
  grep -qiE 'RESOLVED|FIX LANDED|NOT A BUG|CLOSED|WONTFIX|FIXED' "$f" || echo "$f"
done | wc -l      # -> 22
```

**Open: 22.** First pass found 25; **three closed while this was written** —
`const_generic_argument_rejected_in_constructor_call_2026-08-17`,
`struct_field_dict_mutation_through_free_function_is_a_noop_2026-08-10`, and
`stage2_cross_module_codec_result_field_inference_2026-08-14`.

**Method rule for this document: no hardware claim is inherited from a bug doc.**
Every "hardware-gated" verdict below cites the probe run on this box on
2026-08-17. Where no probe was run, the row says **claimed, unverified**.

---

## Host capability probe — measured 2026-08-17

| Capability | Probe | Result |
|---|---|---|
| NVIDIA GPUs | `nvidia-smi --query-gpu=name,memory.total,driver_version --format=csv` | **RTX A6000 49140 MiB** + **TITAN RTX 24576 MiB**, driver **580.126.16** |
| GPU device nodes | `ls /dev/nvidia*` | `nvidia0`, `nvidia1`, `nvidiactl`, `nvidia-modeset`, `nvidia-fs0..15` — all present |
| Container toolkit | `which nvidia-container-cli docker` | `/usr/bin/nvidia-container-cli`, `/usr/bin/docker` — both present |
| Vulkan, real driver | `vulkaninfo --summary` | TITAN RTX and RTX A6000 both enumerate, `driverName = NVIDIA`, `apiVersion 1.4.312`; `llvmpipe` also present as a third device |
| Software rasteriser | `ls /usr/share/vulkan/icd.d` | `lvp_icd.json` present (lavapipe) alongside `nvidia_icd.json` |
| **Intel GPU** | `lspci -nn \| grep -i vga` | **absent** — exactly two VGA controllers, `10de:2230` (GA102GL) and `10de:1e02` (TU102), both NVIDIA. `intel_icd.json` is installed but has no device to attach to. |
| QEMU OpenGL | `nm -D /usr/bin/qemu-system-x86_64 \| grep -c egl_display` | **0** — and `qemu-system-x86_64 -device virtio-gpu-gl,help` still fails `undefined symbol: qemu_egl_display` **with two working NVIDIA GPUs present**. Proof this is a QEMU *link-time packaging* defect, not a GPU-absence problem. |
| QEMU system emulation | `ls /usr/bin/qemu-system-*` | `aarch64`, `arm64`, `arm`, plus the full set |
| Firmware | `ls /usr/share/OVMF /usr/share/AAVMF` | `OVMF_CODE_4M.fd` etc. **and** `AAVMF_CODE.fd` etc. — the x86_64 and aarch64 real-firmware lanes of `.claude/rules/board-runnable.md` are both available here |
| PowerVR UAPI header | `find / -name 'pvr_drm.h' -o -name 'drm_pvr*'` | **no results** |
| RISC-V board | host `uname -m` = `x86_64`; no board on this machine | absent (QEMU/OpenSBI available for development) |
| Apple / macOS | n/a | absent |

---

## Blockers that were FALSE

Docs whose stated blocker this host already satisfies, or which blamed the wrong
thing. **These are immediately actionable.**

1. **`render_perf_8k80_completion_aggregator_missing`** — claims it needs "the
   NVIDIA CUDA/Vulkan container host". **This box IS that host** (probe above:
   two NVIDIA GPUs, real driver, container toolkit, device nodes). Also the
   title is wrong: the aggregator is *implemented*
   (`scripts/check/check-render-perf-8k80-container.shs`, contract test passing);
   only the A4/A5 receipts are missing. → **PENDING (host-verifiable).**
2. **`vulkan_8k_jit_retained_host_buf_sample_crash`** — reads as GPU-gated; the
   workload runs on pinned lavapipe (`lvp_icd.json` present) and real NVIDIA
   Vulkan is available besides. Nothing about it is unavailable here.
   → **PENDING (host-verifiable).**
3. **`board_vulkan_lanes_fabricated_counterpart_output`** — the lanes' own stated
   reason ("needs a verified process-exec capability from pure Simple, which
   wasn't available") is **false**: `process_run_bounded`
   (`src/lib/nogc_sync_mut/io/process_ops.spl:76`), `process_run_with_limits`
   (`:414`), `process_run` (`src/lib/nogc_sync_mut/io_runtime.spl:170`), and
   `exec_to_evidence` (`src/lib/common/spec/evidence/format/exec_capture.spl:142`)
   all exist and are exported. `vulkaninfo` works here against both NVIDIA and
   lavapipe. → **PENDING (host-verifiable).**
4. **`host_qemu_virtio_gpu_gl_missing_egl_symbol`** — filed as a hardware/GPU
   blocker for B0/venus. It is **not**: the symbol is missing from the QEMU
   binary itself, and re-probed today *with two working NVIDIA GPUs attached* it
   still fails identically. A GPU cannot supply a symbol the ELF never exported.
   This is a QEMU rebuild, free, on this box. → **PENDING (host-verifiable).**
5. **`img_bxe_submit_encoder_envelope_only`** — filed as PowerVR-hardware-gated.
   The near-term blocker is an **upstream header**, not silicon: vendoring
   `struct drm_pvr_job` closes the byte-layout question with no device.
   → hardware needed only for the final end-to-end validation.
6. **`riscv_gen2_sequential_hwir_selfhost_runtime_blocker`** — reads RISC-V, so
   reads board-gated. Its evidence is generated-VHDL + GHDL **simulation**; no
   RISC-V silicon is involved at all. → bootstrap-gated, not hardware-gated.
7. Outside this open set, same lesson: the **SIMD gate** blamed `objdump` when the
   real cause was a malformed regex; the **AOT lane** blamed uncommitted
   cross-session work when the real cause was two committed defects (now green
   again at `3463d698fee`, which unblocks the draw_ir 8K, gui 8K, and fat32
   verification paths); a **coverage** doc's title misattributes the layer; and
   `disk_image_fat32_builder_defects.md` suggests the wrong primitive.

---

## Summary

### Counts by class

| Class | Count | Bugs |
|---|---:|---|
| **fully closed** | 7 | dns_aaaa_qtype, simple_timeout_seconds_ignored, blink_specs_import, stage4_bootstrap_rust_inputs_changed, riscv_gen2_sequential_hwir, a2_target_ir_untracked_target_graph, silent_deletion_audit |
| **source fixed / admitted or external evidence pending** | 11 | lint_timeout_hwir_zca_rows, bootstrap_stage2_silent_exit1, board_vulkan_fabricated_counterpart, host_qemu_virtio_gpu_gl_missing_egl, render_perf_8k80_aggregator, vulkan_8k_jit_retained_host_buf_sample_crash, stage4_resume_from_admitted_gap, cmdstream_boundary_no_intel_gpu, img_bxe_submit_encoder, starfive_check_deployed_simple_segv, process_transfer_session_replay_identity |
| **bootstrap-admission gated** | 2 | stage3_selfhost_exit_139, stage3_post_file_copy_exit139 |
| **owner-decision** | 2 | app_interpreter_deletion_evidence_package, app_interpreter_tree_declared_removed |

### Machines and environments actually required — ranked by payoff

**Rank 0 — Linux QEMU/virgl host required for final evidence:** the portable
probe now classifies loader-symbol mismatch, OpenGL-disabled, device-absent,
and ready states. Homebrew QEMU 10.2.2 on this Apple Silicon host reports
`device-absent`; it cannot close the original Linux QEMU 8.2.2 module/main
binary mismatch.

**Rank 1 — NVIDIA host required for final 8K evidence:** this Apple Silicon
host has Metal 4 and no `nvidia-smi`. The aggregator and retained-array source
fixes are green, but NVIDIA Vulkan and 7680x4320@80 receipts remain external.

**Rank 2 — completed source half:** the PowerVR `drm_pvr_job` layout is pinned
to Linux commit `8d3ae59288f1e7d58d76558a6ee96d533bc5019f` and encoded by the
checked-in UAPI layout owner. Firmware/device submission validation remains
external.

**Rank 3 — 1 bug — x86_64 Linux host with a discrete Intel Gen12/Xe-LP GPU**
(a Tiger Lake / Alder Lake laptop or NUC, or an Arc A-series card; plus
`mesa-utils`, `intel_error_decode`/`aubinator`/`intel_dump_gpu`, and `render`
group membership). *Why that machine:* `INTEL_DEBUG=bat` decodes batch buffers
Mesa `anv` submits **to a live Intel device**; NVIDIA does not satisfy this
because the boundary under test is Intel's MI_*/3DSTATE_* command-stream
encoding, which no other vendor emits. *QEMU sufficient?* **No** — there is no
emulated Intel GPU that produces a real `anv` batch stream. *Fix vs verification:*
the **fix** (writing the encoder, which does not exist at all) is host-work today;
only the **counterpart capture** needs the silicon.

**Rank 4 — 1 bug — physical RISC-V board, StarFive VisionFive 2-class (JH7110).**
The doc does not pin a model; the constraint is a JH7110-class board running the
deployed full CLI with a serial console. *Why:* the SIGSEGV is in a binary
deployed on that board. *QEMU sufficient?* Development yes — QEMU + OpenSBI is
available here per `.claude/rules/board-runnable.md`; final evidence needs the
board. *Caveat before buying:* the failing executable path recorded in the doc is
`x86_64-unknown-linux-gnu`, so **try reproducing it here first** — it may not be
a board bug at all.

**Rank 5 — 1 bug — PowerVR Rogue/BXE-4-32 silicon** with a matching firmware
release, for `img_bxe` end-to-end validation only. *QEMU sufficient?* **No** —
submission is firmware-mediated; there is nothing to emulate.

**Not required by any open bug:** Apple Silicon / Intel Mac, aarch64 native host
(QEMU + EDK2/AAVMF is present and sufficient here), FreeBSD host (the repo's
QEMU wrapper covers it), Windows host, a physical display for 8K evidence (the
physical-presentation receipt is **optional** in the A7 contract).

### Current host result

All evidence-backed source corrections identified by this sweep are now
implemented, including Blink paint and production process-session
authentication. Rows 4/5/6/9/10/11/12/22 still require receipt-bound admitted
execution; rows 7/8/16/17/18 need the explicitly named external runtime or
hardware evidence; rows 19/20 still require an owner deletion decision and
were not changed destructively.

---

## Per-bug entries

### 1. `dns_aaaa_query_qtype_not_28_2026-08-17.md` — CLOSED (stale spec offset; 35/35 green)
- **Current resolution:** encoder was correct; the spec read QTYPE two bytes
  late. The corrected exact and adjacent all-type offset oracles supersede the
  suspected library root cause and old fix guide below.
- **Symptom:** `AAAA query has QTYPE=28` asserts truthy, gets `0`; 34/35 in `dns_spec.spl`.
- **Root cause:** suspected, localised. `DNS_TYPE_AAAA` is declared in `src/lib/nogc_sync_mut/dns/types.spl` and imported by `wire.spl`; the field is left unset or the accessor reads the wrong offset. Only visible now because a phantom `use string.{char_from_code}` import in `wire.spl` masked it until `3d56c94653e`; that fix touched the label/TXT *decode* path, so this is pre-existing, not a regression.
- **Fix guide:** stdlib only — **no engine choice, no build** (`src/lib/**` is read as source every run). In `src/lib/nogc_sync_mut/dns/wire.spl`, make the AAAA query builder write `DNS_TYPE_AAAA` into the QTYPE bytes; check the reader offset the spec uses.
- **Reproduce here:** `bin/simple test test/01_unit/lib/nogc_sync_mut/dns/dns_spec.spl` → expect 35/35. Sabotage: write 27, expect RED.
- **Hardware:** none — host-fixable. **Unblock:** nothing.

### 2. `simple_timeout_seconds_ignored_by_light_daemon_budget_2026-08-17.md` — FIXED (`dc8545a772`)
- **Current resolution:** env/default parsing, flag precedence, and
  daemon-no-response inconclusive classification are implemented. The bullets
  below retain the original reproducer context.
- **Symptom:** `SIMPLE_TIMEOUT_SECONDS=840` still dies at `budget_ms=120000` with `reason=daemon-no-response` and `failed=1`; `--timeout 800` on the same spec passes. High tooling-honesty severity: 6 of 17 formal-verification specs were recorded RED this way in one sweep.
- **Root cause:** known by location — `src/app/test_runner_new/test_runner_client.spl` and `src/app/test_daemon/light_protocol.spl`; the flag path sets the budget, the env path does not.
- **Fix guide:** pure-Simple only (`src/app/**`); the Rust seed is not involved. Make the code path that `--timeout` feeds also read `SIMPLE_TIMEOUT_SECONDS` (×1000) when the flag is absent, flag winning on conflict. Separately, a daemon no-response must emit an INCONCLUSIVE verdict, never `failed=1`.
- **Reproduce here:** `SIMPLE_TIMEOUT_SECONDS=840 timeout 900 bin/simple test test/00_formal_verification/compiler/lean_basic_spec.spl` (currently 0/1 timeout) vs `bin/simple test … --timeout 800` (4/4). Fix = both give 4/4.
- **Hardware:** none. **Unblock:** nothing.

### 3. `blink_specs_import_unimplemented_modules_2026-08-10.md` — CLOSED (`00920d22fe`; all four owners green)
- **Current resolution:** form state, input event/hit-test, and the shared Skia
  recorder/DisplayList paint walker are implemented. Focused counts are 4/4,
  8/8, 7/7, 6/6, 3/3, and 8/8; the missing-module guide below is historical.
- **Symptom:** four blink specs RED, `semantic: Cannot resolve module: std.blink.dom.form_state` and siblings.
- **Root cause:** known — feature gap, not a compiler defect. **[false blocker]** the reported `STATICS_FAILED_KEY` failure mode was console-noise misreading; that constant is `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:298` and is unrelated. A separate still-unfiled defect is documented there: the `Use <> instead of [] for generics` warning is a **false positive** on dict bracket-assignment (`handles[K] = 1`, line 305), emitted on every parse of the compiler tree.
- **Fix guide:** write the missing `std.blink.dom.*` modules (`form_state` + the three other `geo.*`/`BoxModel` dependants) under `src/lib/`. Stdlib, no build. Then file the bracket-assignment warning separately.
- **Reproduce here:** `SIMPLE_TIMEOUT_SECONDS=3600 bin/simple test test/01_unit/lib/blink` — currently `89 total, 52 passed, 37 failed`.
- **Hardware:** none. **Unblock:** nothing.

### 4. `lint_timeout_hwir_zca_rows_2026-08-17.md` — SOURCE FIXED / RECEIPT-BOUND PURE-SIMPLE TIMING PENDING
- **Current resolution:** the conservative required-comment admission gate is
  implemented. Only timing with a receipt-bound pure-Simple CLI remains; the
  suspected profiling guide below predates that fix.
- **Symptom:** lint of `src/compiler/50.mir/hwir/zca_rows.spl` exceeds **900s** (re-verified worse than the 600s at filing), no verdict line, log frozen at 382 lines.
- **Root cause:** suspected — superlinear per-decl lint cost. Measured: 1901 lines, 30 function decls; the published model (~11.7s startup + ~3.3–4.0s/decl) predicts ~130s, so observed is **~7× above even the linear prediction**. The published cost model under-predicts badly here.
- **Fix guide:** profile `bin/simple lint` on this one file (sampling profiler or in-linter timing counters); the likely shape is a per-decl pass rescanning all prior decls. Fix in **pure-Simple** (`src/app/lint` / the lint pass in `src/compiler`) — the seed cannot be the fix target since no pure-Simple binary can lint today. Correct `.claude/rules/commands.md`'s cost model afterwards.
- **Reproduce here:** `nice -n 19 timeout 900 sh scripts/check/lint-cached.shs src/compiler/50.mir/hwir/zca_rows.spl` — **CPU-bound for 15+ min; do not run while a bootstrap is compiling.**
- **Hardware:** none — but wants an idle box. **Unblock:** CPU time.

### 5. `bootstrap_stage2_silent_exit1_empty_log_2026-08-17.md` — SOURCE FIXED (`17b9c0d72d`) / LIVE MID-BUILD RECEIPT PENDING
- **Current resolution:** cadence progress always writes and flushes stderr
  before optional event-file handling. A live redirected admitted build must
  still prove the log grows mid-build.
- **Symptom:** stage2 exits 1 with a **0-byte** `stage2-native-build.log`. Status MITIGATED (a diagnostic block now distinguishes the three silent cases); the root defect is open.
- **Root cause:** **known.** Replay against `build/phase_snapshots/phase1_1786935122/simple` proved the restricted `env -i` sandbox does *not* break the seed (`--version`, `native-build --help` both exit 0). The defect is that `native-build` writes **nothing** to a non-tty stdout/stderr until completion or a flushed error — 580s of real CPU work with a 0-byte log throughout. `SIMPLE_BUILD_PROGRESS_EVENTS` is a file path, not a verbosity flag, so it yields no progress evidence either.
- **Fix guide:** line-buffer or explicitly flush progress/diagnostics when stdout is not a tty — a tty check is selecting full buffering. Pure-Simple driver (`src/app/cli`, `src/compiler/80.driver`).
- **Verify here:** rerun the transcript's exact command redirected to a file; the log must grow *during* the build, not only at exit.
- **Hardware:** none. **Unblock:** nothing.

### 6. `board_vulkan_lanes_fabricated_counterpart_output_despite_available_exec_api_2026-08-11.md` — SOURCE FIXED (`1358b28f0c`) / LIVE WORKER RECEIPT PENDING
- **Current resolution:** the Lavapipe owner launches the pinned compiled worker
  through bounded process evidence and rejects missing/empty/nonzero output.
  The literal/provider replacement guide below is complete.
- **Symptom:** none of the eight board-Vulkan boundary lanes ever executed an open-source counterpart; every "comparison" ran against bytes the lane authored itself. L2 device enumeration returns a hand-typed lavapipe literal at `boundary_enumeration_provider.spl:104-137`; L4's measured hashes were gathered by the agent's own shell, not the spec.
- **Root cause:** **known, and the lanes' stated cause is false** — see "Blockers that were FALSE" #3 for the four exported exec/evidence APIs with file:line.
- **Fix guide:** delete the literal at `boundary_enumeration_provider.spl:104-137`; have the spec invoke `vulkaninfo` through `process_run_with_limits` and feed the output to `exec_to_evidence`. Same for the L4 inventory hashes. L3's receipt gate is already sound and sabotage-proven; it just needs a real `libvulkan_lvp.so` invocation behind it.
- **Reproduce here:** `vulkaninfo --summary` works against both NVIDIA devices *and* lavapipe (`lvp_icd.json` present) — probe-confirmed today. **No GPU acquisition involved; lavapipe is CPU-side.**
- **Hardware:** none. **Unblock:** nothing.

### 7. `host_qemu_virtio_gpu_gl_missing_egl_symbol_2026-08-11.md` — PORTABLE PROBE FIXED / LINUX VIRGL EVIDENCE PENDING
- **Current resolution:** a bounded portable capability checker now classifies
  the exact symbol mismatch and adjacent disabled/absent/failure states.
  Homebrew QEMU on this Mac is `device-absent`; Linux virgl remains external.
- **Symptom:** `qemu-system-x86_64: -device virtio-gpu-gl,help: failed to open module: hw-display-virtio-gpu-gl.so: undefined symbol: qemu_egl_display`. Blocks B0/venus before venus can be evaluated.
- **Root cause:** **known — QEMU packaging, NOT hardware.** Ubuntu `1:8.2.2+ds-0ubuntu1.17` does not export `qemu_egl_display` from the main binary; none of the 6 `.so`s in `qemu-system-modules-opengl` export it either, so all three `*-gl.so` device modules fail to load — with or without `-display egl-headless`, regardless of `venus=on`. `libvirglrenderer1` 1.0.0 *is* installed.
- **Probe (2026-08-17, decisive):** `nm -D /usr/bin/qemu-system-x86_64 | grep -c egl_display` → **0**, and the device help still fails **with two working NVIDIA GPUs and `/dev/nvidia*` present**. A GPU cannot supply a symbol the ELF never exported. The doc's implied hardware framing is false.
- **Fix guide:** build QEMU from source with `--enable-opengl --enable-virglrenderer` (EGL/GBM/virglrenderer dev packages), or take a build where the symbol exists. Verify with `nm -D` on the new binary and a succeeding `-device virtio-gpu-gl,help`. Then attempt B0/venus **via the OVMF-pflash path** (`/usr/share/OVMF/OVMF_CODE_4M.fd` is present) — never `-kernel`, per `.claude/rules/board-runnable.md`.
- **Hardware:** none — free on this box. **Unblock:** an OpenGL-enabled QEMU build.

### 8. `render_perf_8k80_completion_aggregator_missing_2026-08-14.md` — AGGREGATOR FIXED / NVIDIA 8K EVIDENCE PENDING
- **Current resolution:** the aggregator and Darwin-portable positive/sabotage
  self-test are green. This Apple Silicon host has no NVIDIA device; the old
  “this box has RTX A6000 + TITAN RTX” statement below describes another host.
- **Symptom:** A7 (the parent-authoritative decision over the DrawIR + Vulkan + optional-physical receipts) has no live correlation, so green rows could be combined manually across mismatched viewport, damage class, revision, device, or provenance.
- **Root cause:** **known, and the title is wrong.** The aggregator IS implemented — `scripts/check/check-render-perf-8k80-container.shs`, with a passing bounded-positive and deliberate-red contract test. Missing: live native A4 (CPU DrawIR) and A5 (strict Vulkan) receipts for the same 7680×4320 workload. **Nothing to fix in source.**
- **Blocker was false:** the doc says this needs "the NVIDIA CUDA/Vulkan container host". Probe: this box has RTX A6000 + TITAN RTX, driver 580.126.16, `nvidia-container-cli`, `/dev/nvidia*`, and `vulkaninfo` enumerating both with `driverName = NVIDIA`. **It is that host.**
- **Fix guide:** run the existing wrapper with explicit DrawIR, producer, optional-physical, and report inputs. It must correlate A4 and A5 for the same workload/damage class/revision/provenance, requiring p95 ≤ 12.5 ms, nonzero RSS/checksum, exact readback scope, and no disallowed fallback. Contract: `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` §0-B A7; owner TODO811. The AOT lane going green at `3463d698fee` unblocks the draw_ir 8K path feeding A4.
- **Hardware:** none — already present. A physical display is needed only for the **optional** presentation receipt, which A7 does not require. **Unblock:** run it.

### 9. `vulkan_8k_jit_retained_host_buf_sample_crash_2026-08-12.md` — OWNER FIXED (`fda534d0dd`) / STRICT-JIT 8K RERUN PENDING
- **Current resolution:** retained mirror samples are now read inside the
  concrete Engine2D VulkanBackend owner, with exact 64-row and invalid-index
  regressions. Strict-JIT 8K execution remains pending admitted capacity.
- **Symptom:** the retained Vulkan 8K workload completes 200 timed frames, then strict JIT SIGSEGVs when the harness samples `VulkanBackend.host_buf` for readback parity. Peak RSS 2,137,920 KiB. The preceding run (before direct sample assertions) gave p50 1,040,146 ns / p95 1,539,488 ns, 3,276,800 transfer bytes, zero full fallbacks — but an invalid **zero checksum**.
- **Root cause:** unknown, **narrowed by a negative result**: `test/fixtures/jit_class_u32_array_retained_read/main.spl` — same 33,177,600-element `[u32]`, class field, 210 frames of mutation, aliased, first/changed/last reads under strict JIT — **passes**. So plain class-field `[u32]` retained reads are not the defect; something Vulkan-specific (mirror lifetime, or the host-visible mapping) is.
- **Fix guide:** extend that reduction toward the real shape (add the host-visible mapping and the strided 64-row mirror transfer) until it reproduces. Required closure per the doc: isolate class-field array borrowing vs direct indexed access vs retained-mirror lifetime; add a strict-JIT regression reading first/middle/last from a class-owned `[u32]` after repeated mutation; preserve a nonzero checksum or an explicit sampled-parity receipt. Engines: JIT in `src/compiler/70.backend` **and** the Vulkan SFFI in `src/compiler_rust/runtime/src/value/gpu_vulkan/` — both, since the crash straddles them. **Never substitute an expected checksum for the missing proof**; a timing-only row is not an admissible 8K/80 pass.
- **Reproduce here:** viewport 7680×4320, pinned lavapipe (`lvp_icd.json` present), one 64×64 damage rect, 10 warmup / 200 timed frames, `SIMPLE_JIT_STRICT=1`. Needs ~2.1 GiB RSS — trivially available.
- **Hardware:** none — lavapipe is CPU-side, and real NVIDIA Vulkan is present besides. **Unblock:** nothing.

### 10. `stage3_post_file_copy_exit139_2026-08-14.md` — FIX IMPLEMENTED / STAGE 3 VERIFICATION PENDING
- **Symptom:** Stage 3 exits 139 in a high-memory region after lowering `dir_create_all`/`file_copy`, then again entering statement 1 of `eval_binop`.
- **Root cause:** **known and symbolized.** GDB stack: `MirLowering.remember_local_hir_type` ← `maybe_copy_array_value` ← `lower_stmt_impl` ← `lower_block_expected`. `maybe_copy_array_value` passes a `HirType` aggregate into another native method; under the Stage 2 ABI that aggregate transport corrupts the callee — the already-proven static-receiver class. Source: **`src/compiler/50.mir/mir_lowering_types.spl:414`**. GDB log `build/native_probe/stage3-gdb/gdb.log` SHA `25f6fb3c…`.
- **Fix guide:** the repair is already written — `copy_local_hir_type_metadata(source_id, destination_id)`, scalar args only, copying the aggregate inside the owning aligned arrays, rejecting the same nil/raw-zero sentinel `find_local_hir_type` does. `sh scripts/check/check-native-scalar-metadata-copy.shs` passed once with an admitted pure-Simple compiler on 2026-08-16. **Only Stage-3 verification remains.** Engine: pure-Simple `src/compiler/50.mir`.
- **Fix vs verification:** the **fix is written**; only evidence is missing.
- **Hardware:** none — needs a multi-hour uncontended bootstrap. **Unblock:** a clean full Stage-3 run.

### 11. `stage3_selfhost_exit_139_2026-08-14.md` — bootstrap-gated
- **Symptom:** fresh pure-Simple Stage 2 segfaults (139) compiling Stage 3; the driver console was not retained, so exit 139 is an **unretained observation, not a hash-bound receipt**.
- **Root cause:** unknown. Explicitly distinct from `stage3_selfhost_post_hir_segfault_2026-08-14.md` — different source authority, output dirs, candidate hashes, retention. The doc forbids attributing one run's evidence to the other.
- **Fix guide:** re-run the recorded `bootstrap-from-scratch.sh --pure-simple --full-cli --no-mcp --diagnostics=test …` command **retaining the console**, then symbolize under GDB exactly as bug 10 did. Retained Stage 2: `build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, SHA `7617c924…`. The crash is in the **pure-Simple** Stage 2 compiler, so any fix lands in `src/compiler`, not the seed.
- **Hardware:** none. **Unblock:** a retained, reproducible Stage-2→Stage-3 diagnostic run (likely the same defect as bug 10).

### 12. `stage4_resume_from_admitted_gap_2026-08-14.md` — FIXED (`f32fc3ebcb`; live continuation pending authority)
- **Current resolution:** the resume path, immutable Stage2/3 snapshots,
  planner/provenance/lock gates, and installed-vs-candidate hash equality are
  implemented. Only an admitted Stage3+planner live continuation remains.
- **Symptom:** Stage 4 cannot continue from an admitted, already-built Stage 3.
- **Root cause:** known — the canonical wrapper has no `--resume-stage4-from-admitted=<output>`.
- **Fix guide:** fully specified in the doc. Add the flag to `scripts/bootstrap/bootstrap-from-scratch.sh`, requiring a planner-authored `//bootstrap:stage4` typed-reason receipt, validating the Stage 3 candidate + provenance manifest, acquiring the output lock, binding a continuation-lock receipt **without mutating Stage 2/3**, then entering the existing Stage 4 / essential-tools / provenance / deployment gates. Candidate repair `scripts/bootstrap/resume-stage4-from-admitted.sh`, sourced only after receipt validation. `SimpleBootstrapStage4ContinuationV1` binds planner receipt + Stage 3 manifest/candidate + lock + snapshot. Acceptance: Stage 2/3 hashes unchanged; provenance verifier green before any Stage 4 process; `bin/release/x86_64-unknown-linux-gnu/bootstrap-deploy-receipt.env` records `schema=bootstrap-deploy-receipt-v1` / `deployment_status=pass`; **no Rust seed row accepted as Stage 4 evidence.**
- **Fix vs verification:** the implementation is host-work today; only live acceptance is blocked.
- **Hardware:** none. **Unblock:** an admitted Stage 3 lane + planner receipt (bug 10 landing).

### 13. `stage4_bootstrap_rust_inputs_changed_2026-08-15.md` — RESOLVED (intended fail-closed authority rejection)
- **Symptom:** `--full-bootstrap --deploy` aborts with `Rust inputs changed during full bootstrap; refusing to publish a stale seed`; zero Simple files ever compiled.
- **Root cause:** known — **a provenance failure, not a compile failure.** 17 dirty `src/compiler_rust/**` paths (across `common`, `compiler`, `parser`, `runtime`, `native_all`); ordered dirty-path fingerprint `91339a9a75…`.
- **Fix guide:** **Rust seed engine only.** Land or revert the 17 dirty paths so the tree is quiescent, re-take the fingerprint, and start the full bootstrap from a clean checkout so the guard cannot fire mid-run. **Do not weaken the guard** — refusing to publish a stale seed is correct. Verify: the run reaches Stage 2 source discovery with a nonzero Simple file count.
- **Hardware:** none. **Unblock:** a quiescent `src/compiler_rust/` tree — contested by parallel sessions, which is the real blocker.

### 14. `riscv_gen2_sequential_hwir_selfhost_runtime_blocker_2026-08-14.md` — CLOSED (current pure-Simple runtime green)
- **Current resolution:** the sequential datapath implementation and exact
  mixed/standalone regressions are green; the stale-runtime blocker below is
  retained only as history.
- **Symptom:** the bounded test-ABI probe rejects the deployed `release/x86_64-unknown-linux-gnu/simple`; `check src/compiler/50.mir/hwir/sequential.spl` exits 139; canonical `bin/simple` entry absent.
- **Root cause:** suspected — same deployed-self-host miscompile class as bugs 10/21.
- **Fix guide:** nothing to change in source in this lane. Deploy a provenance-admitted self-hosted **Stage 4** CLI whose bounded test-ABI probe passes, then run each exact resume command once from `.spipe/riscv_gen2_hwir_foundation/state.md`, retaining outputs and coverage. Sources when actionable: `src/compiler/50.mir/hwir/sequential.spl`, `src/compiler/70.backend/backend/hwir_to_vhdl.spl`, `test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl`. **Neither the Rust seed nor a Stage-2 compiler is admissible as qualification evidence** — `bin/simple` here still prints the seed banner.
- **Hardware:** **none, despite the RISC-V name.** The evidence is generated-VHDL + GHDL **simulation**, pure software; no RISC-V silicon is involved. **Unblock:** Stage-4 deploy.

### 15. `a2_target_ir_blocked_on_untracked_target_graph_2026-08-10.md` — RECOVERED / FIXED (`df2e577a89`)
- **Current resolution:** the compute-only owner landed independently at
  `src/compiler/80.driver/cache/target_ir.spl`; 9/9 exact/adjacent tests pass.
  The untracked-worktree coordination account below is superseded.
- **Symptom:** a complete, green Wave-1 target IR (9 `TargetKind`s, 9 typed edge kinds, `TargetLabel` parser, `build.sdn` reader, `TargetGraph`) is deliberately withheld from `main`.
- **Root cause:** known and social. A2 authored it as an **append** to `src/compiler/80.driver/cache/target_graph.spl`, which is **untracked** — another session's in-flight 281-line file (`git cat-file -e <origin-tip>:…` exits 128). Landing it would commit someone else's unfinished work, which `.claude/rules/vcs.md` forbids.
- **Fix guide:** do not rebase or force the append. Either (a) the other session lands `target_graph.spl` first and A2 re-applies on top, or (b) A2's IR moves to a **new tracked file** (e.g. `src/compiler/80.driver/cache/target_ir.spl`) with no textual dependency on the untracked one — (b) is available immediately and is the recommended path. Work lives in worktree `.claude/worktrees/agent-a5cdacdf7286b11a3` — **do not delete it.**
- **Verify:** `test/01_unit/compiler/build_graph/target_graph_spec.spl` 9/9, with the two recorded sabotage probes (rdeps returning the forward closure; malformed `//path` accepted) going RED.
- **Hardware:** none. **Unblock:** the concurrent session landing or abandoning its file — or choosing (b) and unblocking immediately.

### 16. `cmdstream_boundary_no_intel_gpu_on_capture_host_2026-08-11.md` — SOURCE FIXED / LIVE INTEL ANV EVIDENCE PENDING
- **Current resolution:** the Gen12/Xe encoder and canonical adapter are
  implemented with five green source suites. Only live ANV capture/submit/
  readback remains; the “no encoder” bullets below are superseded.
- **Symptom:** `vulkan.submit.command_stream@1` (lane R4 / SoC B3) cannot be exercised.
- **Root cause:** known, **two independent blockers**. (1) **No candidate:** `src/os/drivers/gpu/board_vulkan/backend_intel_gen12.spl` declares `spirv_implemented`/`submit_implemented`/`readback_implemented` all `false`, and `board_profile_false_claim` in `soc_profile.spl` correctly rejects a profile claiming `submit` without `spirv`; there is **no command-stream encoder anywhere** under `board_vulkan/`. (2) **No capture hardware.**
- **Probe (2026-08-17):** `lspci -nn | grep -i vga` → exactly two controllers, `10de:2230` and `10de:1e02`, **both NVIDIA**. `intel_icd.json` is installed but has no device. Confirmed absent.
- **Machine class:** x86_64 Linux host with a discrete **Intel Gen12 / Xe-LP** GPU — a Tiger Lake / Alder Lake laptop or NUC, or an Arc A-series card. Plus `mesa-utils`, `intel_error_decode` / `aubinator` / `intel_dump_gpu`, and `render`(993) group membership.
- **Why that machine, and why NVIDIA does not substitute:** the boundary under test is Intel's MI_*/3DSTATE_* batch-buffer encoding. `INTEL_DEBUG=bat` decodes batches Mesa `anv` submits **to a live Intel device**; no other vendor emits that stream. The two NVIDIA GPUs here are irrelevant to it.
- **QEMU sufficient?** **No.** There is no emulated Intel GPU producing a real `anv` batch stream.
- **Fix vs verification:** the **fix** — writing the Gen12 encoder from the public PRM — is host-work available today; only the **counterpart capture** needs silicon. Flip the profile flags honestly as each stage lands; **never set `submit_implemented` before `spirv_implemented`**, the guard exists for that.
- **Unblock:** encoder implementation (host, now) + Intel silicon (acquisition, for evidence) — independently.

### 17. `img_bxe_submit_encoder_envelope_only_no_kernel_uapi_verification_2026-08-11.md` — UAPI SOURCE FIXED / POWERVR VALIDATION PENDING
- **Current resolution:** the exact Linux UAPI layout is pinned and encoded
  fail-closed, including indirect sync arrays, alignment, and HWRT rules. The
  missing-header probe and vendoring guide below are superseded.
- **Symptom:** the IMG BXE-4-32 submit encoder carries a self-consistent dword layout never checked against the real kernel UAPI.
- **Root cause:** known. PowerVR submission is **firmware-mediated**: work goes through `DRM_IOCTL_PVR_SUBMIT_JOBS` / `struct drm_pvr_job`, and the *firmware*, not the GPU core, interprets the CCB control stream, whose `pvr_rogue_fwif*` format is versioned per firmware release. Unlike Adreno CP packets or Intel MI_*/3DSTATE_*, it is not a stable encodable ISA. The encoder honestly encodes only the envelope (job type, context handle, HWRT handle, sync-op fences, stream length) and labels the CCB payload `opaque_firmware_blob` — **nothing was fabricated.** Files: `src/os/drivers/gpu/board_vulkan/encoder_img_bxe.spl`, `test/01_unit/os/vulkan/img_bxe_encoder_layout_spec.spl`.
- **Probe (2026-08-17):** `find / -name 'pvr_drm.h' -o -name 'drm_pvr*'` → **no results**; the header is genuinely absent from this host.
- **Environment, not silicon (near-term):** vendor the upstream `drivers/gpu/drm/imagination` UAPI header, or cite a pinned upstream revision, then re-derive `img_bxe_job_field_offset` / `img_bxe_sync_op_offset` against its real offsets and update the layout spec. **A text file, no machine.** Do not synthesize CCB bytes.
- **Machine class (validation only):** a board with PowerVR Rogue / BXE-4-32 silicon and a matching firmware release. **QEMU sufficient? No** — firmware-mediated submission has nothing to emulate.
- **Unblock:** vendor the header (near-term) → PowerVR hardware (full validation).

### 18. `starfive_check_deployed_simple_segv_2026-08-15.md` — HOST RECURSION FIXED / REDEPLOY + JH7110 EVIDENCE PENDING
- **Current resolution:** the recorded crash belonged to an x86_64 deployed
  runtime, not a JH7110 execution. Recursive release delegation now fails
  closed without Rust-seed substitution; redeploy and board evidence remain.
- **Symptom:** `bin/simple check src/lib/nogc_async_mut/fs_driver/ramfs.spl` exits 139 before any source diagnostic, on deployed `/home/yoon/simple/release/x86_64-unknown-linux-gnu/simple` SHA `04a38e21d6…`.
- **Root cause:** suspected — the known deployed self-host environment-write/miscompile class referenced by `scripts/lib/simple-compiler-select.shs`; same family as bugs 10/14.
- **Fix guide:** repair the deployed full CLI — i.e. land bug 10's MIR aggregate-transport fix, redeploy, re-run `check` on the StarFive implementation files. **Do not substitute the Rust seed.** Scope has already shrunk: this no longer blocks the board build or physical acceptance (an admitted pure-Simple Stage 3 builds the ELF and the canonical contract/self-test/live checker passes); it blocks only running the generated SSpec through the deployed CLI.
- **Machine class:** a physical **StarFive VisionFive 2-class (JH7110)** RISC-V board with a serial console. The doc does not pin a model — the real constraint is "a JH7110-class board running the deployed full CLI".
- **QEMU sufficient?** Development yes — `qemu-system-riscv64` + OpenSBI per `.claude/rules/board-runnable.md`. Final evidence needs the board.
- **Probe caveat, check before buying:** the failing executable path is `x86_64-unknown-linux-gnu`, so the SEGV may reproduce **on this box** with that deployed binary. Try that first; it may be misfiled as a board bug.
- **Unblock:** seed/stage redeploy, then board access.

### 19. `app_interpreter_deletion_evidence_package_2026-08-11.md` — owner-decision
- **Symptom:** decision package for deleting `src/app/interpreter/`. Zero engineering unknowns remain.
- **Root cause:** known, fully measured (re-measured 2026-08-17 at HEAD): 100 files on disk, 99 tracked, **0 untracked residue**, 1.1 MB, 25,232 lines, 62 of 99 using the rejected `from X import {…}` form. Repo total 114,545 tracked files, so a 99-file removal is 0.086% — **inside the tree-size guard's ±0.15% band; no `--expect-files` override needed.** External compile-time imports: **zero** (`git grep "use app.interpreter"` outside the tree returns 0 lines).
- **Fix guide:** on an owner "yes", delete the tree and in the **same commit** fix the two real dependants: `test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl:41,48` (reads `src/app/interpreter/core/watchdog.spl` and asserts on substrings) and `test/03_system/feature/interpreter/runtime_error_stack_spec.spl:73` (`run_interpreter(["src/app/interpreter/main.spl", …])`). The other 13 mentions are inert. Verify with the pre-push guards, especially `check-tree-size-push.shs`.
- **Hardware:** none. **Unblock:** owner decision — delete vs migrate.

### 20. `app_interpreter_tree_declared_removed_but_still_on_disk_2026-08-10.md` — owner-decision
- **Symptom:** the package is declared removed yet is on disk and still compiled. This is the **original diagnosis**; the decision lives in bug 19 §0.
- **Root cause:** known, with two measured findings that kill the obvious workarounds. (1) Removing the eager `from actors import {…}` in `__init__.spl` does **not** decouple — the compiler compiles *every* `.spl` in a package directory, so `reserved keyword 'actor' cannot be used as a parameter name` (`actors.spl:59:19`) persists. (2) With `actors.spl` moved aside the build advances one step and dies on `from mailbox import {…}` → `semantic: variable 'from' not found`. **`actors.spl` was never the blocker.** Supersedes the diagnosis in `88b3874cd51` and the header comment in `test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl` (and its `test/unit/` twin).
- **Fix guide:** merge into bug 19's decision. If the owner picks migration, the work is rewriting 62 files off `from X import {…}` onto `use module.{…}` plus renaming the `actor` parameter — 25k lines, which is why deletion is on the table.
- **Hardware:** none. **Unblock:** same owner decision as bug 19.

### 21. `silent_deletion_audit_2026-08-11.md` — CLOSED (all 12 rows reverified)
- **Current resolution:** every row was reverified and the runtime API guard now
  protects the restored surface. The rerun/closure guide below is complete.
- **Symptom:** audit of silent mass deletions across the 343 commits landed 2026-08-10 12:00 → 2026-08-11 on origin/main; 12 commits flagged (thresholds: ≥300 total deletions, ≥200 lines from one file, or ≥40 files changed).
- **Root cause:** known per row. **[stale]** Row #3 re-verified 2026-08-17: `src/compiler_rust/runtime/src/value/collections.rs` is back at **6148 lines / 210 `fn rt_*`** with `rt_array_reduce` and `rt_array_free_deep` present — the audit's "STILL MISSING" verdict for `6e2f613d302` (recorded 4211/198) is stale. **Do not double-restore.** Row #1 `ad2b5d5307f` *is* the restore commit.
- **Fix guide:** re-run the audit's own method (`git log --numstat` over the window; per-path pre/post/current-tip line counts plus symbol-set diffs), close every RESTORED-SINCE row, escalate only rows still short at HEAD, then mark the doc closed. `check-runtime-api-regression-push.shs` now guards this class going forward.
- **Hardware:** none. **Unblock:** one verification pass and a closure marker.

### 22. `process_transfer_session_replay_identity_2026-08-12.md` — PRODUCTION SOURCE FIXED / ADMITTED EXEC EVIDENCE PENDING
- **Symptom:** the native transfer allocator's RegionId (low 31 PID bits + 32-bit local sequence in a positive `i64`) gives no global uniqueness across PID namespaces, PID reuse, stale frame replay, or process restarts.
- **Root cause:** known by design. The bounded frame decoder verifies route, destination, length, and an FNV-1a corruption checksum — **FNV-1a is a corruption check, not authentication.**
- **Current source:** HMAC-SHA256 wire authentication, parent-issued epoch/namespace/PID/generation identity, and cancellation revocation are integrated into `parent_commit_piped_process.spl`. Its `SPRF2` reader authenticates before the existing generation/replay inbox. The exec-isolated scenario covers valid admission, wrong-session rejection, exact replay rejection, and cancellation; V1 remains an explicit compatibility constructor.
- **Hardware:** none. **Remaining evidence:** redeploy an admitted pure-Simple CLI and run the focused native system scenario once.
