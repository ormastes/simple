# M4 — LLVM lane (asan, memprof): feasibility + insertion-point design

Predecessor: `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`
(M4 scope), `doc/02_requirements/runtime/memory_analysis/feature_backend_memory_infra_toggle.md`
(capability matrix — `asan`/`memprof` = LLVM-only, "no" under
interpreter/cranelift). M3 (`--mem-infra=` resolver) has **not landed yet** —
no `BUILD:asan`/`BUILD:memprof` markers exist in the tree. This doc gives M3
a concrete target, per `m2_guard_and_harden_design.md`'s own precedent
("becomes the CLI alias once M3 lands").

## 1. Feasibility — LLVM lane cannot build Stage-2/3 today

`doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md`
+ `.claude/rules/bootstrap.md`: the seed's LLVM backend link fails on
stage-2 native-build of the self-hosted compiler (62 undefined
method-call/compiler-internal symbols after a partial fix); Cranelift is
the working stage-2/3 path. **Biggest blocker for M4**: `asan`/`memprof`
are LLVM-gated by design, but LLVM can't self-host a Stage-2/3 binary, so
M4 can't be exercised on the bootstrap path — only on ordinary
`native-build --backend=llvm` of small user `.spl` programs that avoid the
missing-symbol set. Prerequisite for anything beyond toy fixtures: close
the 62-symbol gap, or (cheaper) keep M4's exit criterion scoped to a small
standalone `.spl` corpus, never "the compiler compiling itself" — exactly
what the plan doc already says ("stage-2 compile of a small corpus").

## 2. Where `-fsanitize=address` would be injected

Clang's `-fsanitize=address` = (a) AddressSanitizer LLVM passes over the IR
(redzone instrumentation) + (b) linking `libclang_rt.asan`. Neither is a
plain "add a flag" here: `LlvmBackend` is in-process LLVM via `inkwell`
(`compiler/Cargo.toml:18`, `llvm = ["inkwell"]`) — MIR → LLVM IR → object
bytes, no clang/llc subprocess compiles Simple source. clang/llc
subprocesses only appear at **link** time and in a few support tools.

**Part A — instrumentation pass.** The backend already runs an explicit
new-PM pipeline: `codegen/llvm/backend_core.rs:118-143`
(`fn optimize_module_ir`) builds `PassBuilderOptions` and calls
`module.run_passes(pipeline, target_machine, options)` at line 141,
`pipeline` picked from opt level (`"default<O1/O2/O3>"`, lines 134-138).
Called once, from `fn compile` (starts line 1312) at line 1149, right
before `write_to_memory_buffer` (line 1153). Open question, not assumed:
does LLVM's new-PM text parser accept ASan's pass names
(`asan`/`asan-module`) via bare `LLVMRunPasses`, without clang driver-side
setup ASan also leans on? Needs a spike (a cargo unit test in
`codegen/llvm_tests/`, which already has `object_emission.rs`) before
committing. **Fallback if it fails:** the backend already has a text-IR
escape hatch — `SIMPLE_DEBUG_LLVM` dumps `.ll` via `llvm.get_ir()` at
`pipeline/native_project/compiler.rs:647-652`; an asan build variant could
emit `.ll` and shell to `opt -passes=asan,asan-module` + `llc` instead.

**Part B — linking the ASan runtime.** Plain flag injection at an existing
call: `pipeline/native_project/linker.rs:1180` (`fn link_objects`, main
link path, `Command::new(&cc)`) is where `-fsanitize=address` would be
appended so the driver links `libclang_rt.asan`. `cc` is already resolved
via `target_c_compiler`/`target_cxx_compiler` (lines 1173-1177); gating on
`backend == "llvm"` (the capability matrix's own scoping) is enough.

**Config carrier.** `NativeProjectConfig` (`native_project/mod.rs`) already
carries `pub backend: String` (line 329, default `"cranelift"`) and
`pub opt_level: NativeOptimizationLevel` (line 343), threaded into
`LlvmBackend::new_with_opt_level_and_cpu` (`compiler.rs:634`) and the
linker. A sibling `pub mem_infra: Vec<String>` is the natural carrier for
M3's resolved matrix; `compiler.rs:634` and `linker.rs:1180` (which already
reads `self.config.linker_script` at line 1196) are its two consumers.
**This field does not exist yet — M3's job to add; M4 only consumes it.**

## 3. `memprof` — output + "store the profile" v1

`-fmemory-profile` uses the same pass family as ASan
(`MemProfilerPass`/`ModuleMemProfilerPass`) and writes a raw profile
(`memprof.profraw`, path via `MEMPROF_OPTIONS=log_path=...` — same
env-control pattern as `ASAN_OPTIONS` in
`scripts/check/cert/sanitizer-matrix.shs:380-390`). Turning that into a
`.memprofdata` for `-fmemory-profile-use=` (PGHO feedback) needs
`llvm-profdata merge` and is explicitly out of scope (plan's WATCH: "LLVM
PGHO feed-back once the allocator grows partitioning hooks").

**Minimal v1:** same two hook points as asan (§2 parts A/B) plus pointing
`MEMPROF_OPTIONS=log_path=<dir>/<binary>.profraw` at run time and landing
the raw file under `build/mem_infra/memprof/` for M8 to read later. No
parsing, no PGHO consumer — that would be scope creep past M4's own exit
line ("profile stored for future PGHO feed-back", not "consumed").

## 4. Interim alternative on cranelift today: real but partial

`scripts/check/cert/sanitizer-matrix.shs` **already does this, not
hypothetically**: `runtime_selfcontained_tus()` (line 181) finds every
self-contained `src/runtime/*.c` TU (excludes `vendor/`), and
`runtime_smoke`/`runtime_full` (lines 253-343) compile each with
`-fsanitize=address -fno-sanitize-recover=address -g -O1` (line 148) plus
run a generated self-check harness under the sanitizer (lines 274-283) —
a live-instrumentation proof, not just build-clean.

**Assessment: real value, narrower than "sanitize a cranelift-built Simple
program."** It genuinely covers bugs in the hand-written C runtime
(`rt_alloc`, string/collection helpers) — cheap, no LLVM dependency, works
today. It does **not** cover Cranelift-emitted `.spl` object code, which
carries zero ASan instrumentation; linking an instrumented runtime against
uninstrumented generated code gives interceptors but no redzone/UAF
detection on accesses *from Simple-compiled code*. That gap is M2's job
(backend-agnostic guard pages/quarantine), not ASan's. Keep the existing
runtime-only gate — it's real — but don't read it as "M4 done on
cranelift"; M4's actual target (instrumenting generated code) stays
LLVM-only and blocked by §1.

## 5. Test plan / blocked split

**Not blocked (cranelift-independent, buildable today):**
- `sanitizer-matrix.shs --san=address --target=runtime` stays the
  runtime-C-only gate (§4) — already exit-code gated, no new work.
- `MEMPROF_OPTIONS`/`ASAN_OPTIONS` env-propagation plumbing through
  `native_project`'s test-build path (per-process env precedent at
  `tools.rs:205-231`) — testable against any LLVM-backend `native-build`
  of a plain user `.spl` binary; doesn't need seed self-hosting.
- The §2 `optimize_module_ir` pipeline-string spike, as a cargo unit test
  in `codegen/llvm_tests/`, checked for `__asan_*` calls in emitted IR.

**Blocked on the LLVM stage-2 bug
(`seed_stage2_llvm_method_symbol_lowering_2026-07-17.md`):**
- Any M4 exit criterion whose "corpus" means the compiler compiling
  itself — link fails before asan/memprof get a chance to run.
- Full bootstrap-path `--backend=llvm` verification stays cranelift-only
  per `.claude/rules/bootstrap.md`; M4 fixtures must be a small standalone
  `.spl` corpus via direct `native-build --backend=llvm`, not the
  bootstrap wrapper, until the bug closes.
- M8 reading a real Stage-2/3 memprof profile — blocked the same way;
  reads small-corpus fixture profiles meanwhile.

## Insertion-point summary

| What | File:line |
|---|---|
| Pass-pipeline injection | `codegen/llvm/backend_core.rs:118` `optimize_module_ir`, called line 1149 in `fn compile` (line 1312), before `write_to_memory_buffer` (1153) |
| Text-IR fallback | `pipeline/native_project/compiler.rs:647-652` (`SIMPLE_DEBUG_LLVM`) |
| ASan link flag | `pipeline/native_project/linker.rs:1180` `fn link_objects`, `cc` at 1173-1177 |
| Config carrier (M3 to add) | `pipeline/native_project/mod.rs:329` `backend` / `:343` `opt_level` — sibling `mem_infra` |
| Existing runtime-C ASan gate | `scripts/check/cert/sanitizer-matrix.shs:181,253-343` |
