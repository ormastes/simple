# Feature: pure_simple_profile_guided_executable_optimization_2026-06-01

## Raw Request
$sp_dev complete pure_simple_profile_guided_executable_opti....md

## Task Type
feature

## Refined Goal
Complete the pure-Simple profile-guided executable optimization slice so native profile counters, reloadable `.sprof` data, pure-Simple layout planning, and bare-metal breakpoint profiling have executable evidence and restartable documentation.

## Acceptance Criteria
- AC-1: Native profile-counter builds expose durable sidecar metadata and can convert observed counter snapshots into reloadable `.sprof` profile files.
- AC-2: The optimize layout bridge consumes executable metadata plus a reloadable `.sprof` profile and writes a deterministic pure-Simple layout manifest without invoking external BOLT.
- AC-3: The pure-Simple executable layout planner preserves manifest validity, separates hot and cold functions deterministically, and rejects unsafe transforms.
- AC-4: Bare-metal breakpoint profiling covers patch, trap, count, restore, rearm, cleanup, invalid patch, missing icache flush, and sampled-only fallback behavior.
- AC-5: SPipe specs and generated manuals exist under the correct `test/` and `doc/06_spec/` locations, with no executable `.spl` specs under `doc/06_spec`.
- AC-6: Focused checks and specs pass for the profile loader, native counters, layout bridge, executable layout planner, and bare-metal breakpoint profiler.

## Scope Exclusions
- Arbitrary ELF rewriting outside Simple-owned settlement/native metadata.
- Hardware-only bare-metal speedup claims without QEMU or hardware evidence.
- Full release automation unless explicitly requested after verification.

## Phase
complete

## Log
- dev: Reconstructed missing SPipe state file with six testable acceptance criteria.
- codex: Repaired profile-layout bridge coverage to prove reloadable `.sprof` file consumption into an output manifest.
- codex: Re-ran focused checks/specs; loader, native counter, layout bridge, executable layout, and bare-metal breakpoint specs passed.
- codex: Audited command-level native smoke. Imported effect self-test `main` functions are renamed in the current tree, but `llvm_direct.spl --simple-profile-counters` still aborts with a `simple-main` stack overflow before writing the binary or metadata sidecar; tracked in `doc/08_tracking/bug/llvm_direct_run_entrypoint_misdirected_2026-06-01.md`.
- codex: Current focused verification remains green: checks pass for `effects.spl`, `effects_solver.spl`, `sprof_loader.spl`, `profile_layout_cli.spl`, `native_profile_counter.spl`, and `llvm_direct.spl`; profile loader, native counter, profile layout, executable layout, and bare-metal breakpoint SPipe specs all pass. Goal is not complete until command-level native smoke is proven or explicitly descoped.
- codex: Narrowed command-level blocker. Removing the unused `app.compile.native.find_cpp_compiler` import from `llvm_direct.spl` avoids the stack overflow, but the command still cannot emit C: `driver.driver` lacks runtime `aot_c_file`, the lazy codegen helper cannot resolve `compiler_driver_create` under script execution, and `simple compile --backend=c` currently writes SMF bytes while `--native --backend=c` is rejected. The native profile-counter command smoke remains unproven.
- codex: Re-ran focused verification after narrowing: six scoped checks passed; SPipe specs passed for sprof loader (23), native profile counters (30), profile layout CLI (8), executable layout (15), and bare-metal breakpoint profile (22); `git diff --check` passed for scoped files; `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- codex: Resolved command-level native smoke by removing the stale `compiler.backend.wffi_bindgen` package export and routing `llvm_direct.spl` through `compiler.driver.driver_api.aot_c_file`. Minimal and `_codegen_smoke.spl` runs now emit native binaries plus durable `<output>.simple-profile-counters` sidecars.
- codex: Converted observed counter snapshots to reloadable `/tmp/simple_pgo_smoke.sprof`, then ran `src/app/optimize/main.spl --layout-plan --profile=/tmp/simple_pgo_smoke.sprof --manifest=/tmp/simple_pgo_smoke.layout --out=/tmp/simple_pgo_smoke.optimized.layout`; the deterministic manifest clustered `main`, `make_text`, and `make_obj` hot and `make_gpu` cold without invoking external BOLT.
- codex: Completion audit passed. Required compiler/lib/MCP gates passed (`check src/compiler`, `check src/lib`, `check src/app/mcp`, `check src/app/simple_lsp_mcp`, MCP stdio integration). Focused specs passed: sprof loader 23, native profile counters 30, profile layout CLI 8, executable layout 15, bare-metal breakpoint profile 22. `git diff --check` passed, placeholder-test scan found no matches, `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`, and `sh scripts/install-spipe-dev-command.shs --check` returned `STATUS: PASS`.
- codex: Added final feature and NFR requirement artifacts, deleted the unchosen `_options.md` files, and recorded NFR evidence in `doc/09_report/pure_simple_profile_guided_executable_optimization_2026-06-01.md`. Current measurements: profile-load startup overhead 2.6% against an import-equivalent baseline; native profile-counter runtime overhead 2.1% over 1000 native process runs.
