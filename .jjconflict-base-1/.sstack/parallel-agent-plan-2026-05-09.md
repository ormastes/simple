# Parallel Agent Plan — Blockers & Remaining Work

**Date:** 2026-05-09
**Scope:** All remaining sstack pipelines + pass_todo stubs

---

## 1. Blocker Summary

| Blocker Category | Count | What's Needed |
|-----------------|-------|---------------|
| Skia native FFI | 65 pass_todo | Skia C++ library bindings (canvas, colrv1, vulkan, text) |
| Torch FFI | 72 pass_todo | PyTorch/libtorch C bindings for tensor ops (sum, mean, prod, min, max, std, norm, etc.) |
| GPU runtime | 14 pass_todo | GPU compute runtime (builtins.spl) |
| ASM / C port | 1 pass_todo | RISC-V32 assembly context switch (context.spl:96) |
| Runtime extern | ~10 pass_todo | chr(), sleep, IPC, syscalls (os/tools/*, intrinsics, nvfs) |
| Compiler sugar (B4) | ~3 pipelines | Pattern matching, bitfield sugar, advanced generics |
| SIMD FFI | 1 pipeline | Runtime SIMD intrinsics for compression/cipher |
| Design wave | ~5 pipelines | Need research/arch phases before implementation |
| Massive scope | ~3 pipelines | Wine/Proton, scilib, RTL — too large for single agent |
| Test baseline | ~3 pipelines | Need stable test runner / compiled mode |

**162 of 167 pass_todo stubs are blocked** on FFI/runtime that doesn't exist yet.
Only ~5 OS tool stubs are potentially addressable (base64, top, netstat, ifconfig, pkg_cli).

---

## 2. Wave 1 — Actionable Agents (5 parallel, disjoint scopes)

These 5 sstack pipelines have phases 1-4 complete (or can start from scratch) and operate on **non-overlapping file sets**.

### Agent A: fix-warning-and-allow

| Field | Value |
|-------|-------|
| **sstack** | `.sstack/fix-warning-and-allow/` |
| **Starting phase** | 5-implement (phases 1-4 done) |
| **File scope** | Files with `@allow` suppressions (~753 across codebase) |
| **Task** | Remove @allow suppressions by fixing the underlying warnings. 9 categories: unused-var, unused-import, unused-fn, shadow, type-mismatch, naming, unreachable, deprecated, unsafe. |
| **Exit criteria** | @allow count reduced by ≥50%; remaining ones justified with inline comment |
| **Parallelism notes** | Touches many files but only @allow lines; low conflict risk if other agents avoid @allow edits |
| **Estimated effort** | Medium — mostly mechanical deletion + minor refactoring |

### Agent B: debug-format-verify

| Field | Value |
|-------|-------|
| **sstack** | `.sstack/debug-format-verify/` |
| **Starting phase** | 5-implement (has internal 7-agent wave plan) |
| **File scope** | `src/compiler/*/debug_format*.spl`, `test/unit/compiler/debug_format*.spl` |
| **Task** | Fix interpreter-mode bugs in debug format output; add spec coverage. Internal plan: Wave 1 (A: fix debug_format_core, B: fix debug_format_ext), Wave 2 (C-F: per-format specs), Wave 3 (G: integration). |
| **Exit criteria** | All debug format specs pass in interpreter mode |
| **Parallelism notes** | Fully contained in compiler/debug_format files — no overlap |
| **Estimated effort** | Medium — interpreter bug workarounds + test writing |

### Agent C: rename-sspec-to-spipe

| Field | Value |
|-------|-------|
| **sstack** | `.sstack/rename-sspec-to-spipe/` |
| **Starting phase** | 1-dev (all phases pending) |
| **File scope** | All files containing "sspec" string — filenames, imports, references |
| **Task** | Full mechanical rename: `sspec` → `spipe` across the entire repo. Includes file renames, import path changes, string references, doc updates. |
| **Exit criteria** | Zero occurrences of "sspec" (except git history); all tests pass |
| **Parallelism notes** | **HIGH CONFLICT RISK** — touches files across entire repo. Must run AFTER or BEFORE other agents, not truly concurrent. Best as a final consolidation step or first step before others. |
| **Estimated effort** | Low complexity, high file count — ~2-3 hours of mechanical work |

### Agent D: m13-float-css-quickwins

| Field | Value |
|-------|-------|
| **sstack** | `.sstack/m13-float-css-quickwins/` |
| **Starting phase** | 5-implement (phases 1-4 done) |
| **File scope** | `src/lib/gc_async_mut/gpu/browser_engine/layout/float*.spl`, `src/lib/gc_async_mut/gpu/browser_engine/css/float*.spl`, `test/unit/browser/css/float*.spl` |
| **Task** | Implement CSS float layout improvements to raise WPT pass rate from 37.8% → 65%+. Focus on: float clearing, margin collapsing with floats, float intrusion into line boxes. |
| **Exit criteria** | WPT float subtree pass rate ≥65%; no regressions in non-float tests |
| **Parallelism notes** | Contained in browser_engine/layout + browser_engine/css float files — no overlap |
| **Estimated effort** | High — CSS layout is complex; needs careful WPT verification |

### Agent E: bug-sweep-2026-04-26

| Field | Value |
|-------|-------|
| **sstack** | `.sstack/bug-sweep-2026-04-26/` |
| **Starting phase** | 5-implement (phases 1-4 done) |
| **File scope** | Bug-specific files (varies per bug) |
| **Task** | Fix remaining bugs from the 2026-04-26 sweep. Each bug is independent — naturally parallel within itself. |
| **Exit criteria** | All identified bugs fixed or documented as blocked with specific blocker |
| **Parallelism notes** | Per-bug scope; low conflict unless bug touches same file as another agent |
| **Estimated effort** | Variable — depends on remaining bug count and complexity |

### Wave 1 Execution Order

```
┌─────────────────────────────────────────────────────────┐
│ OPTION 1: rename-first (safer)                          │
│                                                         │
│ Step 1:  [C: rename-sspec-to-spipe] ──────────────────► │
│                                                         │
│ Step 2:  [A: fix-warning] ──┐                           │
│          [B: debug-format] ─┤  (parallel)               │
│          [D: css-float]    ─┤                            │
│          [E: bug-sweep]    ─┘                            │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ OPTION 2: rename-last (faster, riskier)                 │
│                                                         │
│ Step 1:  [A: fix-warning] ──┐                           │
│          [B: debug-format] ─┤  (parallel)               │
│          [D: css-float]    ─┤                            │
│          [E: bug-sweep]    ─┘                            │
│                                                         │
│ Step 2:  [C: rename-sspec-to-spipe] ──────────────────► │
└─────────────────────────────────────────────────────────┘
```

---

## 3. Blocked Pipelines — Deferred

### 3a. Blocked on Compiler Sugar / Language Features

| Pipeline | Blocker | Detail |
|----------|---------|--------|
| crypto-pure-simple-port | B4 compiler sugar | Needs bitfield ops, pattern matching for cipher round functions |
| compression-cipher-simd-continue | SIMD FFI | Needs rt_simd_* extern functions for vectorized compression |

### 3b. Blocked on Runtime / FFI

| Pipeline | Blocker | Detail |
|----------|---------|--------|
| text-encoding-engine | Research phase incomplete | UTF-8/16/32 codec architecture not designed yet |
| scilib-port | Fortran FFI | LAPACK/BLAS bindings don't exist |

### 3c. Blocked on ASM / C / Hardware

| Pipeline | Blocker | Detail |
|----------|---------|--------|
| simpleos-multiarch-harden | ASM context switch | RISC-V32 context.spl:96 needs inline assembly |
| rtl_riscv_mdsoc_reorg | VHDL toolchain | RTL simulation infrastructure not in Simple |

### 3d. Blocked on Design / Scope

| Pipeline | Blocker | Detail |
|----------|---------|--------|
| wine-proton-steam-impl | Massive scope | Win32 API surface too large for single agent |
| dbfs-integration | Design wave | DBFS architecture not finalized |
| jj-wrapper-daemon | Daemon infra | Needs background process management |
| 2d-engine-backend-research | Research phase | Backend selection not decided |
| check-browser-engines | Research phase | Browser engine comparison not complete |

### 3e. Blocked on Test Infrastructure

| Pipeline | Blocker | Detail |
|----------|---------|--------|
| test-failures-round2 | Test baseline | Needs stable compiled-mode test runner (R2-broader) |
| tls-live-bug-fix-restart | TLS integration | Needs live TLS server for testing |

### 3f. Partially Complete / Low Priority

| Pipeline | Status | Detail |
|----------|--------|--------|
| simpleos-fs-apps-mdsoc-audit | Audit phase | MDSOC compliance review, mostly doc work |
| llm-dashboard-harden | Hardening | Security review of LLM dashboard |
| simpleos-serial-log-via-log-lib | Integration | Serial→log-lib bridge, small scope |
| simpleos-primitive-apps | ✅ Complete | 30 apps implemented (phases 1-8 done) |

---

## 4. pass_todo Stubs — Breakdown by Addressability

### 4a. BLOCKED (162 stubs — cannot implement now)

| Location | Count | Blocker |
|----------|-------|---------|
| `src/lib/nogc_sync_mut/src/tensor.spl` | 72 | Torch FFI (scalar reductions, view ops) |
| `src/lib/skia/entity/canvas.spl` | 19 | Skia C++ FFI |
| `src/lib/skia/feature/glyph/colrv1.spl` | 18 | Skia COLRv1 FFI |
| `src/lib/gc_async_mut/gpu/builtins.spl` | 14 | GPU compute runtime |
| `src/lib/skia/backend/vulkan/backend.spl` | 10 | Vulkan FFI |
| `src/lib/skia/entity/paint.spl` | 6 | Skia FFI |
| `src/lib/skia/feature/text/paragraph.spl` | 5 | Skia text FFI |
| `src/lib/skia/feature/text/font.spl` | 4 | Skia font FFI |
| `src/lib/skia/feature/path/*.spl` | 3 | Skia path FFI |
| `src/lib/nogc_sync_mut/intrinsics.spl` | 2 | Runtime intrinsics |
| `src/lib/nogc_sync_mut/fs/nvfs_posix/api.spl` | 2 | NVFS design incomplete |
| `src/os/kernel/arch/riscv32/context.spl` | 1 | RISC-V assembly |
| Other skia/* | ~6 | Skia FFI |

### 4b. POTENTIALLY ADDRESSABLE (5 stubs)

| File | Stub | Approach |
|------|------|----------|
| `src/os/tools/base64_tool.spl` | Base64 encode/decode | Use existing `std.common.encoding.base64` |
| `src/os/tools/top_tool.spl` | Process list refresh | Use `launcher_get_process_*` APIs |
| `src/os/tools/netstat_tool.spl` | Network connections | Stub with simulated data (no real IPC) |
| `src/os/tools/ifconfig_tool.spl` | Interface config | Stub with static data (no syscall) |
| `src/os/tools/pkg_cli.spl` | Package list | Use existing package registry |

---

## 5. Recommended Action

1. **Launch Wave 1 agents** (A, B, D, E in parallel; C before or after)
2. **Fix 5 OS tool stubs** as a small parallel agent alongside Wave 1
3. **Document remaining 162 stubs** as blocked with specific FFI/runtime prerequisites
4. **Revisit blocked pipelines** when compiler B4 / runtime SIMD / Skia FFI land

Total actionable work: **5 sstack pipelines + 5 pass_todo stubs** out of 20 pipelines + 167 stubs.
