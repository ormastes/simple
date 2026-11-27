# Memory/perf bug lanes, 2026-11-02

Base: `origin/release/1.0.0`. Lanes `C:/dev/wt/mp-<n>`, implementer Fable, reviewer Opus (high effort), test runner Haiku.
Shared limits: host commit-free >= 24 GB, all lanes combined <= 40 GB heavy runs (queue heavy runs, one at a time), no stage2 whole-program builds.
Off-limits: `C:/dev/simple`, `C:/dev/wt/phase3`, `C:/dev/p3new/linkdry`, `C:/dev/p3new/r11` (read-only for evidence), P3-RUN processes.
Sources must parse on the frozen stage2 (no `expr else: x` on continuation lines, no new syntax); nil/Any only in `unsafe:`.

## 1. Object cache keyed on whole-tree SCV revision (#5797)
- Root cause: `.o.capsule-receipt` and object reuse key carry `scv-revision-v1-<tree hash>`; any file edit invalidates all objects (1350 objects, only 623 modules covered).
- Owner: `src/compiler/80.driver/driver_aot_native_output.spl` capsule freeze/reuse (~1856, 2082, 2373-2447, 2585), `driver_types.spl` capsule identity, `hir_variant_object_key_v1.spl` (#5745).
- TDD: spec builds key for module A, changes an unrelated module B's content, asserts A's key is unchanged (fails today: key embeds tree revision); changing A or a dep interface must change it.
- Fix: per-module key = module MIR/content digest + dep interface digests + target/options/compiler id; keep tree revision only as receipt metadata.
- Risk: medium. A wrong key reuses stale objects in the phase-3 link. Must include dep interface digests and compiler identity.

## 2. Codegen memory not freed per module (~21 GB per 48-module shard)
- Root cause (suspected): `SIMPLE_CODEGEN_MODULE_SCOPE` is opt-in (`backend_helpers.spl:395-411`, `llvm_codegen_adapter.spl:164`, gate at `driver_aot_native_output.spl:4527`); with it off, per-module LLVM IR text/builders and capsule batch data stay alive across the worker's whole shard loop in `build()`.
- Evidence: `C:/dev/p3new/r11/run20*`, `run21-23b` build logs (`[shard] ... worker budget=3800000 kB`, workers observed far above it).
- TDD: spec compiles N small modules in one process and asserts RSS/heap growth after module N stays under a bound (or the per-module scope releases IR handles); red today with default env.
- Fix: make module scope the default for native object codegen (drop each module's IR/text after its .o is written), release capsule batch per module.
- Risk: medium. Scope must not free data that SMF/`Both` paths re-read (coordinate with lane 3).

## 3. Dynload `Both` format disables MIR sharding and staged codegen (#5791)
- Root cause: `native_build_output_plan.spl:8,84` maps dynload to `Both`; `native_build_main.spl:1218-1221` disables MIR shards; `driver_aot_pipeline.spl:492-494` refuses staged codegen because SMF/Both re-iterate `ctx.mir_modules` after codegen. Full MIR set (~12 GB on 23 GB base) stays resident, then sequential codegen grows 35 -> 66 GB.
- TDD: spec asserts the staged-codegen refusal reason for dynload/Both is empty (today: "output format re-reads MIR set").
- Fix: emit the SMF side per batch (or persist the needed MIR summary) so `Both` no longer re-reads the full MIR set; then allow staging and sharding.
- Risk: high for phase 3 if SMF output changes. Keep SMF bytes identical (determinism check on a small closure).

## 4. First object 121-364 s vs 10 s rule
- Root cause: ~145 s of 158 s is before driver `load_sources`: SCV inventory cold init hashes all `--source` roots; runtime C object build not cached across runs; aop_weave ~6 s with 0 modules.
- Owner: `src/app/cli/native_build_main.spl` startup / SCV admission, SCV inventory module, aop_weave phase in `src/compiler/80.driver`.
- TDD: spec on a 1-file closure asserts the inventory hashes only closure files (count), and aop_weave with nothing to weave returns without work; red today.
- Fix: scope SCV inventory to the entry closure (or lazy hash), short-circuit aop_weave, shared runtime object cache dir.
- Risk: medium. Narrower inventory must not drop files the snapshot needs (stale objects).

## 5. llvm-ar command line too long (WA-AR-1, os error 206)
- Root cause: `driver_aot_native_output.spl` ~3226 appends every object path to `args` for `process_run(archiver, args)`; 1414 paths exceed the Windows 32 KiB limit.
- TDD: spec builds the archive args for 1500 long paths and asserts the argv is short and uses `@<rsp>` (red today).
- Fix: write a response file (one quoted path per line) and pass `@file` to llvm-ar / lib.exe; remove after; keep argv for small lists optional.
- Risk: low. Quote paths with spaces/backslashes correctly.

## 6. Parallel codegen pool validation (#5799/#5801)
- Root cause: specs `native_codegen_pool_v1_spec`, `native_codegen_claim_race_stress_spec`, `native_codegen_pool_determinism_spec` never ran. Open review issues in `src/compiler/80.driver/driver_build/native_codegen_pool_v1.spl`: poll loop starts at 10 ms sleep (lines ~336-344), and timeout `rt_process_kill(pid)` (line ~254) kills the shell, not the llc child tree.
- TDD: run each spec (record red); add a case where a job spawns a grandchild and times out, assert the grandchild is gone.
- Fix: blocking wait (`rt_process_wait` with timeout) instead of fixed poll; kill the process tree (Windows job object/`taskkill /T` by PID, POSIX process group); fix spec runnability.
- Risk: medium. Concurrency bug = P0 class; needs the stress spec green repeatedly.
