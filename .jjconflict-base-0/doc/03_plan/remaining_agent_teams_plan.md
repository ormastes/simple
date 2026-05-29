# Remaining Agent Teams Plan

> **Status:** Bootstrap deploy succeeded. Stage 2+4+5 pass. Stage 3 SEGFAULTs (exit 139, LIM-010) -- non-blocking. 7 non-critical files skipped in Stage 4 (cross-module type inference).

---

## Team A: Stage 3 SEGFAULT Fix (LIM-010)

**Root cause:** LLVM static objects in `libsimple_native_all.a` register CLI options at load time; with C++ symbols resolved, constructors run and conflict ("Option 'debug-counter' registered more than once!").

**Current mitigations:**

| Mitigation | Effect |
|---|---|
| Cranelift backend (no LLVM) | Avoids LLVM entirely |
| `strip_llvm_constructors()` in native_project.rs | Strips problematic constructors |
| `LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1` env var | Suppresses ABI checks |
| Stage 3 made non-fatal (exit 2) | Unblocks pipeline |

**Possible real fix approaches:**

1. Use `dlopen()` for LLVM so symbols don't conflict at load time
2. Build LLVM as shared lib not static
3. Symbol versioning/namespacing
4. Use Cranelift exclusively and drop LLVM backend

**Key files:**
- `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`
- `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs`
- `scripts/bootstrap/bootstrap-from-scratch.sh`

**Reference:** `doc/09_report/bootstrap_crash_report_2026_04_01.md`

---

## Team B: Non-Critical Type Inference Fixes

**Problem:** 7 files skipped in Stage 4 with "struct 'ANY' field" HIR errors due to cross-module type resolution failures.

**Affected files:**

| File | Module |
|---|---|
| `theme_sync.spl` | tools |
| `llm_dashboard` | app |
| `web_dashboard` | app |
| `fix/main.spl` | app/fix |
| `lint/main_part2.spl` | app/lint |
| `lint/main_part4.spl` | app/lint |
| `cli_commands_part1.spl` | app/cli |
| `cli_commands_part2.spl` | app/cli |

**Fix pattern:** Create accessor helpers in the same module where the struct is defined, then import helpers instead of direct field access.

**Already-fixed examples:**

| Struct | Helper | File |
|---|---|---|
| `SpanLabel` | `nllerror_format_related()` | `nll.spl` |
| `EasyFix` | `easyfix_id_text()` | `lint_simd.spl` |
| `_CliProcessResult` | `_cli_result_stdout()` | `cli_ops.spl` |

---

## Team C: Untracked Source Files

57 untracked files across 6 directory groups to add to version control.

| Directory | Description | Files |
|---|---|---|
| `src/compiler/40.mono/` | Monomorphization engine | -- |
| `src/compiler/50.mir/` | MIR lowering | 21 |
| `src/compiler/55.borrow/` | Borrow checking | 5 |
| `src/compiler/60.mir_opt/` | MIR optimization | 3 |
| `src/lib/editor/{60.services,70.backend}/` | Editor services + backends | 13 |
| `src/lib/{ffi,format_utils.spl,gc_async_mut/}` | FFI, utilities, GC async modules | -- |

**Total:** ~57 files

---

## Team D: Future Improvements

| Item | Detail |
|---|---|
| Bootstrap speed optimization | Rayon parallelism tuning |
| LLVM Context memory leak fix | `Box::leak` in `backend_core.rs` line 67 |
| `--entry-closure` support | `bootstrap_main.spl` interpreter path |
