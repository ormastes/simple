# Self-hosted SimpleOS target native-build crash

Date: 2026-07-11  
Status: Open  
Severity: P0 — blocks target-native `/usr/bin/simple` payload

## Reproduction

```sh
release/x86_64-unknown-linux-gnu/simple native-build \
  --source examples/01_getting_started \
  --entry examples/01_getting_started/hello_native.spl \
  --backend=cranelift --target x86_64-unknown-simpleos \
  -o build/tmp/simpleos-target-probe
```

Current result: exit 1, `timeout: the monitored command dumped core`, no output.
The deployed `bin/simple` is byte-identical to the Rust release seed and cannot
be used as production evidence. The older self-hosted release recognizes the
native-build command but does not advertise `--target`; current source does
parse the flag in `src/app/io/_CliCompile/compile_targets.spl`.

Three cache-isolated recovery probes using both
`release/x86_64-unknown-linux-gnu/simple` and
`build/bootstrap/full/x86_64-unknown-linux-gnu/simple` exited 1 before writing
any cache file or diagnostic, including a single-thread run with
`SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1 --verbose`. A focused
`check src/app/cli/native_build_main.spl` also dumped core. Per the iteration
guard, do not repeat these commands; the next step is native crash/backtrace
diagnosis or a known-good self-hosted redeploy, not another retry.

## Required result

A cache-preserving self-hosted rebuild must produce a static
`x86_64-unknown-simpleos` ELF for the full `src/app/cli/main.spl` entry closure,
after which
`scripts/os/simpleos-native-build.shs` stages it at
`bin/release/x86_64-unknown-simpleos/simple` without using the Rust seed.

## Verification

Run the target-native hello probe first, then the full bootstrap CLI entry with
the same cache. Require static ELF identity and a non-crashing `--version` run;
host-only or seed-built output does not close this bug.

## Pure-Simple runtime archive blocker

A fresh stage2 compiler now advertises `--emit-archive`, but building the
existing `src/runtime/simple_core` archive skips `core_string.spl` after LLVM
verification fails:

```text
Call parameter type does not match function signature
i64 %call50 = call i64 @rt_enum_new(i64 ..., i64 ..., i64 ...)
```

The production Pure-Simple LLVM declaration sites intentionally use
`rt_enum_new(i64,i64,i64)` because MIR operands are widened. The bootstrap Rust
registry still fixes the same symbol to `[I32,I32,I64]`; changing only the
Simple definition or adding `as i32` casts did not survive MIR lowering. Three
bounded attempts reached the iteration cap, so no further archive build was
run. The partial archive was deleted and must not be used as target runtime
evidence. The Rust registry file is concurrently dirty in another session, so
this lane did not absorb or overwrite that work.

After the enum ABI owner is reconciled across both codegens, rebuild only the
failed Simple-core archive once and require the log to contain zero
`FAILED FILES`; exit code zero alone is insufficient.

## Bounded recovery result

The generic LLVM call emitters now coerce values to each declared parameter
type in both the Rust bootstrap and Pure-Simple libLLVM paths. A focused Rust
bootstrap build of `core_string.spl` then produced a target archive containing
`rt_string_len` with no failed-file marker.

The next complete archive attempt exposed a separate missing scalar-global
declaration for `FUTURE_SIZE`. The Rust LLVM backend now recovers locally
initialized scalar globals from `global_init_values`. An isolated staged
bootstrap passed stage3 after that fix, but its full CLI linked with 806
unresolved-symbol stubs and failed the required `-c 'print(1+1)'` smoke with
empty output. This consumed the third recovery cycle; do not retry this lane
without first removing the unresolved full-CLI closure.

## RV64 database live finding

A live prebuilt-artifact QEMU smoke proved `/health` and `/` return HTTP 200,
but the database sequence returned `OK CREATE` followed by two `ERR table not
found` responses. The RV64 native path therefore lost class-owned mutable state
between connections. The boot DB now uses one bounded module-owned store, which
matches the single-service design; the next current-source RV64 build must
re-run the real CREATE/INSERT/SELECT transcript before AC-2 can pass.

## Diagnosis (2026-07-11)

### Blocker 1 — native-build crash: ROOT CAUSE FOUND (stale linked runtime, not a source bug)

Reproduced the exact repro command under gdb. Real backtrace:

```text
Program received signal SIGSEGV in __strlen_avx2
#1 __add_to_environ (name="SIMPLE_OS_LOG_MODE", value=0x12 <bad ptr>) setenv.c:131
#2 rt_env_set ()
#4 io.cli_ops.env_set ()
#5 io___CliCompile__compile_targets__cli_native_build ()
#6 cli___CliMain__main_and_help__main ()
```

The value pointer is `0x12` = 18 = `len("SIMPLE_OS_LOG_MODE")`. Breaking on
`rt_env_set` shows the **caller passes correct 4-arg fat-pointer args**:
`rdi=key_ptr("SIMPLE_OS_LOG_MODE"), rsi=key_len(18), rdx=val_ptr("on"), rcx=val_len(2)`.
So the call site and `log_mode="on"` are fine.

The crash is *inside* the linked `rt_env_set`. Disassembly of the deployed
binary shows a **2-argument** implementation, `rt_env_set(char* key, char* value)`:

```asm
rt_env_set:  test %rdi,%rdi; je fail        ; if key==0
             test %rsi,%rsi                 ; treats rsi as the VALUE ptr
             lea  ""(%rip),%rax; cmovne %rsi,%rax; mov %rax,%rsi
             mov  $1,%edx; call setenv@plt   ; setenv(key, rsi, 1)
```

It reads `rsi` (which the caller loaded with `key_len=18`) as the value pointer
→ `setenv("SIMPLE_OS_LOG_MODE", 0x12, 1)` → `strlen(0x12)` SIGSEGV. The value
pointer in `rdx` and length in `rcx` are ignored entirely.

Root cause: **the deployed `release/x86_64-unknown-linux-gnu/simple` (built
2026-07-07 08:59) links a stale 2-arg `rt_env_set`.** Current source is already
consistent at the 4-arg fat-pointer form everywhere:
`src/runtime/runtime_native.c:2382`, `src/runtime/runtime.c`, the Rust seed
runtime `src/compiler_rust/runtime/src/value/sffi/env_process.rs:170`, and the
registry `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1503`
(`rt_env_set [I64,I64,I64,I64]`). The 4-arg C runtime landed in commit
`5e36474fde0` on 2026-07-10 03:38 — **after** the deployed binary was built, so
the binary predates the ABI-consistent runtime.

This is NOT a compiler codegen regression and is unrelated to the banked crash
fix `a0697126` (that was `rt_array_get` in `__simple_main`). No source edit is
needed.

Fix plan (no source change; rebuild/redeploy the self-hosted binary):
- Rebuild from current source so the 4-arg `rt_env_set` (and the rest of the
  post-`5e36474` runtime) is relinked, then redeploy over the stale seed:
  ```sh
  bin/simple build bootstrap        # 3-stage self-compile with current runtime
  # then redeploy the produced binary to release/<triple>/simple
  ```
- Verify: rerun the repro `native-build ... --target x86_64-unknown-simpleos`
  and confirm no core dump (env_set reaches setenv with the real "on" pointer).
- Guard idea: add a smoke that calls `rt_env_set` from a native binary before
  trusting a redeploy, so a stale-runtime relink is caught immediately.

### Blocker 2 — rt_enum_new ABI: canonical = C `(i32,i32,i64)`; reconcile the widened declaration

Declarations located:
- C impl (source of truth), identical in both runtimes:
  `src/runtime/runtime.c:1161` and `src/runtime/runtime_native.c:1895` —
  `int64_t rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload)`.
- Rust seed registry: `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:488`
  — `RuntimeFuncSpec::new("rt_enum_new", &[I32, I32, I64], &[I64])` (matches C).
- Pure-Simple LLVM backend deliberately emits the **widened** declaration
  `declare i64 @rt_enum_new(i64, i64, i64)`:
  `src/compiler/70.backend/backend/llvm_backend.spl:463-465` and
  `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:164-166`,
  with an in-code comment: "i64 to match the MIR call operands; the C
  rt_enum_new(i32,i32,i64) reads the low 32 bits." MIR lowering emits widened
  i64 call operands (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:655+`).

Root cause of the archive-build verifier failure: the pure-Simple backend keeps
its `declare` and `call` both at `(i64,i64,i64)`, so its own modules verify. When
the **seed** codegen builds `core_string.spl`, it emits the registry-driven
declaration `(i32,i32,i64)` while the MIR-lowered call is widened
`(i64,i64,i64)` → within one module the declare and call disagree → LLVM
verifier: "Call parameter type does not match function signature". Adding
`as i32` casts did not survive MIR lowering because MIR re-widens operands.

Canonical ABI is C's `(i32,i32,i64)`; the widened form is ABI-safe on x86_64
SysV because `enum_id`/`discriminant` are small and the callee reads the low 32
bits of the same registers — which is exactly why the shipping pure-Simple
compiler already standardized on `(i64,i64,i64)` and works.

Minimal reconcile (recommended): align the seed registry to the widened form the
pure-Simple backend already uses, so the seed's declaration matches its widened
calls:
- Change `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:488` from
  `&[I32, I32, I64]` to `&[I64, I64, I64]`. The real C symbol is unchanged and
  still reads the low 32 bits, so no runtime behavior changes.
- This is a Rust **seed** change → requires a bootstrap rebuild of the seed
  before the archive build sees it:
  ```sh
  # rebuild the Rust seed with the registry change, then:
  bin/simple build bootstrap
  # then rebuild ONLY the failed archive and require zero FAILED FILES
  ```
- COORDINATION: `runtime_sffi.rs` is reported dirty in a concurrent session
  (state.md). Do not edit it in this lane; hand this one-line change to the
  registry owner. Not applied here per that constraint.

Alternative (more invasive, ABI-purist): make the seed truncate the two
discriminant call operands to i32 at the `rt_enum_new` call site so calls match
the `(i32,i32,i64)` declaration. Rejected as the minimal path because the
codebase already committed to the widened convention.

### Follow-up (2026-07-11): stage1 bootstrap failure is a THIRD, distinct crash (llvm-lib backend)

`bin/simple build bootstrap` stage1
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build --source src/app
--entry-closure --strip --threads 1 --timeout 180 --entry src/app/cli/bootstrap_main.spl
-o bootstrap/stage1/simple --backend=llvm-lib`) died with "Compile failed (exit None)"
yet the pipeline **exited 0 — silent failure masking** (needs its own guard/bug).

gdb on the exact command gives:

```text
Thread 3 "compile-bootstr" SIGSEGV
#0 llvm::DataLayout::setAlignment(llvm::AlignTypeEnum, ...)
#1 llvm::DataLayout::reset(llvm::StringRef)
#2 inkwell::module::Module::set_data_layout
#3 simple_compiler::codegen::llvm::backend_core::LlvmBackend::create_module
#5 simple_compiler::pipeline::native_project::compiler::compile_file_to_object
```

Source site: `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs:846`
(`module.set_data_layout(&target_machine.get_target_data().get_data_layout())`).
This is NOT the stale `rt_env_set` crash (this Rust-lineage binary has no
`rt_env_set` symbol at all) and NOT the #131/#133 llc blockers (llc is never
reached). It is deterministic and systemic for `--backend=llvm-lib`: even a
hello-world native-build segfaults identically. Binary statically links
Ubuntu LLVM 18.1.8 (AlignTypeEnum still exists in 18, so no version mixing).
Matches the "native-build cannot emit on ANY backend" broad-regression memory —
bisect, don't patch.

### Binary inventory — what can native-build src/app right now?

| Binary | Status |
|--------|--------|
| `release/x86_64-unknown-linux-gnu/simple` | CRASHES on any native-build (stale 2-arg `rt_env_set`, above) |
| `bootstrap/stage{1,2,3}/simple` (126 KB) | Mach-O arm64 (macOS artifacts) — unusable on Linux |
| `build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple` + `--backend=llvm-lib` | CRASHES (DataLayout SIGSEGV, this section) |
| `build/bootstrap/stage3/...` + `--backend=cranelift` | **WORKS**: hello builds+runs; the full stage1 command with `--backend=cranelift` exits 0 and the output runs `--version` ("simple-bootstrap 1.0.0-beta"). Caveat: output is 26 KB / "1 compiled" — verify the entry closure isn't stub-collapsed before trusting it as a deploy artifact |
| Rust seed `src/compiler_rust/target/bootstrap/simple` + `SIMPLE_BOOTSTRAP=1 --backend=llvm` (forces external llc) | **WORKS** on hello (builds+runs); this is the memory-documented REAL redeploy path |

Definitive minimal redeploy sequence (until the llvm-lib DataLayout crash is bisected):
1. Replay bootstrap stages with `--backend=cranelift` (or via the seed
   `SIMPLE_BOOTSTRAP=1 ... --backend=llvm` llc path) instead of `llvm-lib`.
2. Gate each stage on a real smoke (`--version` + `-c 'print(1+1)'` + the
   `rt_env_set`-exercising native-build repro), since the pipeline currently
   masks stage failures with exit 0.
3. Deploy the passing stage3 to `release/<triple>/simple`; rerun the SimpleOS
   target repro at the top of this file.
4. Separately: bisect the llvm-lib `create_module`/`set_data_layout` SIGSEGV
   (backend_core.rs:846) — broad regression, per-memory "bisect don't patch".

### Status of the blockers
- Blocker 1: diagnosed, no source fix required — stale deployed binary; rebuild
  + redeploy from current source resolves it. Documented above.
- Blocker 2: diagnosed, one-line seed-registry reconcile identified; not applied
  (concurrent-session ownership + bootstrap rebuild required). Documented above.
- Blocker 3 (new, stage1): llvm-lib backend DataLayout SIGSEGV — deterministic,
  systemic; workarounds proven (cranelift / seed llc); bootstrap pipeline also
  masks the failure with exit 0. Documented above.

### Current RV64 target reproduction after runtime-archive fix

The existing pure-Simple stage3 compiler was invoked directly with the current
canonical RV64 source roots (`build/os/generated`, `src/os`, `src/lib`) and the
LLVM target/linker arguments on 2026-07-11. It exited 139 in 4.5 seconds with no
stdout/stderr and did not produce acceptable new target evidence. This was one
target-build attempt; it was not retried.

The OS runner also selected `src/compiler_rust/target/release/simple` before
checking `SIMPLE_BINARY`/`SIMPLE_BIN`. The selector now checks valid explicit
overrides first, preventing a requested pure-Simple compiler from silently
becoming a Rust-seed build.
## 2026-07-12 deployed ABI and bootstrap follow-up

GDB proved the deployed pure-Simple CLI has a stale two-argument `rt_env_set`: current callers supply `(key_ptr, key_len, value_ptr, value_len)`, but the callee passes `key_len` to libc as the value pointer and crashes in `strlen`. Source already has the four-argument ABI, so the remedy is a provenance-recorded redeploy rather than a call-site workaround.

The isolated rebuild removed a duplicate `module_init_symbol`, then exposed a missing `rt_array_len_safe` static registration. `simple_core` now delegates that name to its already-safe `rt_array_len`, and the Rust SFFI registry declares the same one-argument signature. Verification is deferred because the three-cycle cap was reached.
## 2026-07-12 self-host recovery continuation

The missing `rt_array_len_safe` name required three aligned owner surfaces: the native SFFI signature, the seed interpreter dispatch, and the Simple-core implementation. The interpreter handler cannot alias raw `rt_array_len`, because interpreted compiler arrays are `Value::Array`; it now returns their vector length, handles raw runtime arrays, and returns zero for invalid values.

With that fix, fresh stage 2 and self-hosted stage 3 succeeded. The strict full-CLI build reached final link, where the bootstrap stage had not exposed the hosted runtime archive and therefore omitted symbols such as `spl_dlsym`, `rt_process_run_timeout`, and platform GUI functions. Verification awaits a fresh capped cycle.

The 2026-07-15 source follow-up adds the canonical POSIX/macOS/BSD core-C
`rt_process_run_timeout` owner; Windows is fail-closed pending Job Object capture.
This removes one provider gap but does not close the remaining Stage4 profile or
replace the required capped executable verification.

Correction: `rust-hosted` is a removed CLI bundle name, and the Cranelift native-build lane does not switch bundles through `SIMPLE_RUNTIME_PATH`. The full CLI closure must be reduced to supported core dependencies or gain an explicit supported hosted link lane; the ineffective environment workaround was removed.
## 2026-07-12 focused target handoff

After self-hosted stage 2/3 recovery, a direct focused `x86_64-unknown-simpleos` build reached link but the isolated workspace had no current target Simple-core archive, so core runtime symbols remained undefined. This is an invocation/artifact prerequisite failure: the canonical `scripts/os/simpleos-native-build.shs` wrapper builds the target archive first and exports `SIMPLE_SIMPLE_CORE_PATH`. The next fresh cycle must use that wrapper rather than borrowing an archive from another worktree.
## 2026-07-12 focused target rebuilt

The canonical SimpleOS wrapper now creates a missing sysroot before target Simple-core, so fresh workspaces provide the complete runtime link tuple. Restoring `llvm_translate_module_direct_ir` resolved the sole remaining closure symbol. The focused target now builds as a static ELF64 x86-64 executable with SHA-256 `ef40c3ea4486d90b1d71e6b2e86b8da64f7a11dbae94461adad00c9074efc16a`, zero defined uppercase weak symbols, and zero strong undefined symbols.
## 2026-07-12 static LLVM guest-tool relink

Current sysroot inputs require LLC/LLD relink rather than reuse of older binaries. The relinker must include full `libsimple_runtime.a` because current libc calls Simple runtime owners. LLC then narrowed to one strong undefined, `rt_math_pow`; SimpleOS libc now exports that ABI by delegating to its existing freestanding `pow`. Verification awaits a fresh libc/sysroot rebuild and capped LLC/LLD relink.
