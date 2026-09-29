# `native-build` worker dies with SIGILL (`ud2`) at codegen entry, on every build

- **Filed:** 2026-09-26
- **Status:** FIXED 2026-09-26 (hello-world `native-build` exits 0 on cranelift
  and llvm; see "Resolution"). Two follow-ups stay open, listed there. Was:
  blocks Stage 2, therefore phase 1 `--stop-after-stage2`, the local-temp MCP
  redeploy, and every Cortex-M policy-object build
- **Area:** `80.driver` diagnostics + JIT codegen (cranelift and llvm lanes alike)
- **Host:** yoon-note, x86_64-unknown-linux-gnu, 7 GiB RAM
- **Seed:** built 2026-09-26 09:02 from `03553bcb5f6` (= `origin/main` `49389cb10f3`
  plus 13 unrelated Cortex-M files), `Simple Language v1.0.0-rc.1`

## Resolution (2026-09-26) — three stacked defects, two fixed

Bisected with temporary `log_phase`/`print` markers (all reverted) from the
last marker `aot:format:done` down to the exact statement. The SIGILL was the
*third* of three defects, each hiding the one beneath it:

1. **Empty static backend table in the interpreted worker** —
   `src/compiler/70.backend/backend/codegen_factory.spl:27-28`:
   `active_static_backend_table_v1()` returned `len=0`, so
   `select_static_backend_v1("cranelift", [])` answered `PLUG-E-NOTFOUND` and the
   `case Err(...)` arm called `error(...)`. Cause: since the K1 plugin migration
   (`e0fa5ef45e2`, 2026-09-07) the table is installed only by the compiled CLI
   entries (`bootstrap_main.spl:439`, `_CliMain/main_and_help.spl:302`); the
   seed's native-build spawns `simple run src/app/cli/native_build_worker.spl`,
   whose `main` never installed it. It cannot call the usual
   `compiler.driver.bootstrap_k1_selected` either: the interpreter resolves that
   path to the fail-closed stub (`src/compiler/80.driver/bootstrap_k1_selected.spl`,
   probe printed `policy=unselected install=false`), never to the composition.
   **Fix:** `src/app/cli/native_build_worker.spl` imports the committed
   composition by its own path
   (`compositions.kernel_llvm_cranelift.compiler.driver.bootstrap_k1_selected`)
   and runs the same K1 + full-plugin-table preamble as `main_and_help.spl`,
   failing closed with `PLUG-E-TABLE` + the table diagnostic.
2. **`--output-format both` hashed the `--source` DIRECTORY** —
   `src/compiler/80.driver/driver_aot_pipeline.spl` `both` branch used
   `input_files[0]` as the SMF-manifest source. native-build passes
   `[source_dirs..., entry]` (`compile_targets.spl:1200-1203`), and `dynload`
   (the default `build_mode`) selects `Both`, so every default native-build read
   a directory. Until `ec19563b735` (2026-08-26) that was `rt_file_read_text(dir)
   ?? ""` (silently hashed ""); the fail-closed `file_read_result` since then
   turns it into `CodegenError`, worker rc=1. **Fix:** `_driver_entry_source_input`
   picks the first input that `is_file` — the entry in both producers (plain:
   dirs precede the entry; `--entry-closure`: BFS root is first).
3. **The SIGILL itself is in the PARENT's failure relay, not the worker.**
   `timeout: the monitored command dumped core` names the seed `native-build`
   process (`native_build_main.spl`, JIT'd), which traps with `ud2` while
   relaying the worker's failure text (`eprint_bounded` /
   `native_build_print_failure_hints`, the `rt_eprint_str` frames in the gdb
   trace). It is data-dependent: the same worker failure produced rc=132 or
   rc=1 depending only on how much stdout the worker had printed
   (`SIMPLE_COMPILER_PHASE_PROFILE=1` or extra `print`s flipped it to a clean
   `error: native-build worker exited with code 1`). The worker's own spilled
   stderr (`/tmp/native-build-stderr-<pid>-N.log`) always ended cleanly with
   `error: ...`.

   **MITIGATED, not root-caused, 2026-09-26 (later the same day).** Could not
   reproduce a live rc=132 in this session: forcing the worker past its cheap
   `SCV-E-SNAPSHOT` failure into a real compile (to get enough real output to
   plausibly retrigger the trap) took >150s per attempt without finishing on
   this 7.4 GiB host (`CAP_MEM_MAX=4G` under `scripts/resource/run_capped.shs`,
   `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1`), so the fix below is
   **not verified by observing a clean non-signal exit from an actual rc=132
   case** — only by exercising the same relay code path (`eprint_bounded` with
   a 90 KB synthetic stderr, and the real `native-build` clean-failure repro
   from this record's own "Symptom" section) with no crash, both before and
   after.

   What changed in `src/app/cli/native_build_main.spl`:
   - The worker-failure relay (`eprint_bounded`, `native_build_print_failure_hints`,
     the `code != 0` branch, the `code == 0`-but-no-output-file branch, and the
     `SIMPLE_NO_STUB_FALLBACK` violation branch) now writes via
     `std.nogc_sync_mut.io.stderr_ops.stderr_write` (a thin, non-builtin wrapper
     over `rt_stderr_write`) instead of the bare `eprint` statement. `eprint` is
     a compiler builtin that a co-compiled `fn eprint` in
     `std.nogc_sync_mut.io.process_ops` shadows program-wide under the
     interpreter but NOT under native/JIT codegen — two prior, independent
     `eprint`-dispatch defects have this exact shape
     (`doc/08_tracking/bug/stdlib_eprint_shadows_prelude_builtin_program_wide_2026-08-17.md`,
     `doc/08_tracking/bug/eprint_loses_newline_on_jit_and_llvm_backend_2026-08-17.md`),
     so a third one (this SIGILL) landing on the same builtin is a real
     possibility, not proven. Routing through `stderr_write` removes the
     dependency on that dispatch for the whole relay, whether or not THIS
     defect turns out to be dispatch-related.
   - New `native_build_last_diagnostic_line(stderr)` extracts the worker's own
     last matching diagnostic line, and the `code != 0` branch now writes a
     one-line summary (`error: native-build worker exited with code {code}.` +
     `  worker error: <line>`) via `stderr_write` FIRST, before calling
     `eprint_bounded(stderr)` (previously the bulk dump ran first and the
     "exited with code" summary was the LAST statement in the branch, after
     every signal/timeout arm). If the bulk dump traps for any reason,
     including a cause this record has not identified, the essential fact
     now already reached the terminal.
   - Verified (bootstrap seed, `src/compiler_rust/target/bootstrap/simple`,
     built 2026-09-26 14:40): the clean `SCV-E-SNAPSHOT` repro from this
     record's "Symptom" section still exits 1 (not 132) after the change, and
     the front-loaded summary line now appears in stderr BEFORE the
     `!!!!!! NATIVE-BUILD STDERR TRUNCATED !!!!!!` bulk-dump marker, both for a
     small (<12000 byte) and a >90000-byte captured worker stderr.
   - Regression specs (both fail on the pre-fix source, pass on the fix):
     `test/01_unit/app/cli_native_build_main_contract_spec.spl` — "prints the
     worker's own error line before the crash-prone bulk relay" (ordering) and
     "routes the worker-failure relay through the unambiguous stderr_write"
     (dispatch). Both are source-content assertions (`file_read` + `to_contain`
     / `index_of`), matching this spec file's existing convention for this CLI
     entrypoint — they do not and cannot execute the native/JIT path that
     actually traps.

   **Still open:** the exact trapping statement was never directly observed
   in this session (no gdb attach, no reproduced core), so "which statement
   traps" from the original filing is unconfirmed, not fixed. Anyone who can
   reproduce rc=132 again should re-attach gdb with this fix deployed and
   confirm whether it now exits cleanly; if it still traps, the trap is
   somewhere other than the `eprint`/`stderr_write` dispatch difference and
   this mitigation should be noted as insufficient rather than removed (the
   front-loaded summary line is a real improvement regardless: it survives a
   trap wherever it occurs later in the same branch).

Also observed, open: in the `both` branch the `case Err(error)` binding printed
as `<fn:error>` (a `Value::Function` named `error`) — the interpreter resolved
the arm binding to the builtin. Free-function and `val x = match` probes did NOT
reproduce it; the binding at that site is renamed `read_error` so a genuine read
failure now reports its text. The interpreter-side cause is unlocated.

**Proof** (seed `src/compiler_rust/target/bootstrap/simple`, 2026-09-26 09:02):
```
native-build --backend cranelift ... hw.spl   rc=0, out.bin prints "hi"
native-build --backend llvm      ... hw.spl   rc=0, out_llvm.bin prints "hi"
```
Instrumentation was reverted; `git status` shows only the two fix files.

## Symptom

Every `native-build` invocation aborts with **exit 132 (SIGILL, core dumped)**,
including a three-line hello world:

```
printf 'fn main():\n    print("hi")\n' > hw.spl
SIMPLE_BOOTSTRAP=1 SIMPLE_SCV_FREEZE_FALLBACK=1 \
  src/compiler_rust/target/bootstrap/simple native-build \
  --backend cranelift --source . --entry hw.spl -o hw.bin
# -> Illegal instruction (core dumped), rc=132
```

`compile` on the same file is **rc=0** — the crash is specific to the
`native-build` worker path, not the frontend.

## It is not backend-specific and not target-specific

| invocation | rc |
|---|---|
| `native-build --backend cranelift` (x86_64 hello world) | 132 |
| `native-build --backend llvm` (x86_64 hello world) | 132 |
| `native-build --backend llvm --target thumbv8m.main-none-eabi` (policy object) | 132 |
| `compile` (same hello world) | 0 |

## Root cause: `ud2` in JIT'd code reached from `rt_eprint_str`

`gdb -batch -ex run -ex 'bt 12' -ex 'x/2i $pc'` on the worker generation binary:

```
Thread 2 "simple-main" received signal SIGILL, Illegal instruction.
#0  0x000004869a92cf8b in ?? ()      <- JIT'd (anonymous mapping)
#1  0x000004869a311001 in ?? ()      <- JIT'd (anonymous mapping)
#2  0x0000555556f1fa2c in core::io::write::default_write_fmt::<std::io::stdio::StderrLock> ()
#3  0x0000555556ed33ba in rt_eprint_str ()
=> 0x4869a92cf8b:	ud2
```

`ud2` is what cranelift emits for an `unreachable` terminator, so JIT'd Simple
code reached a path the compiler had proved impossible, **on the stderr-write
path**.

The last line the run emits identifies the exact call site — it is cut off
mid-sentence, which is the process dying partway through the write:

```
[WARN] stage3 bootstrap-flat pipeline active at aot:flat_mir_passes:skipped: MIR
lowering, borrow-check, and the flat MIR passes are SKIPPED for all but the
bootstrap entry module. A clean count here
```

That string is built in `log_bootstrap_flat_warning`
(`src/compiler/80.driver/driver_log_helpers.spl:103-113`) as a **six-part `+`
concatenation with a `{site}` interpolation**, then handed to `log_warn` ->
`eprint` -> `rt_eprint_str`. The message is emitted exactly once, guarded by
`_g_bootstrap_flat_warning_emitted` (`:101`), and the crash is deterministic at
that point — the phase log shows `phase=mir` completing first, then this warning,
then the trap.

### The obvious hypothesis was tested and is WRONG

The first hypothesis was that the six-part concatenation produced a corrupt
`text` and that writing it trapped. **Disproved by probe**: replacing the whole
`log_warn(...)` argument with a single literal (`log_warn("PROBE bootstrap-flat
single literal")`) makes the warning **print completely and correctly** — it
appears in the log — and the run **still exits 132**. So that warning is not the
crash site; it is merely the last thing flushed before the trap, and the
mid-sentence truncation in the original run is a stdio buffering artifact, not
evidence of a corrupt string.

The probe edit was reverted; `driver_log_helpers.spl` is unmodified.

### Where it actually dies: codegen entry

With the warning neutralized, the last progress records are:

```
[build] phase=monomorphize ... task_done=4 task_total=6
[build] phase=mir state=running ... done=1 total=1 remaining=0 succeeded=1 task_done=4 task_total=6
[WARN] PROBE bootstrap-flat single literal
<SIGILL>
```

`mir` completes with `succeeded=1`, `task_done` never reaches 5 of 6, and no
`phase=codegen` record is ever emitted. The trap is therefore at **codegen
entry**, between the MIR phase completing and codegen publishing its first
progress line. The `rt_eprint_str` frames in the backtrace are a diagnostic
write in progress at that moment, not the fault's origin; frames above `#1` are
unreliable because JIT frames carry no unwind info.

## Verified NOT caused by the Cortex-M lane in the same tree

The tree also carries an unrelated M-profile triple change touching
`llvm_target.spl`, `llvm_ir_builder.spl`, and
`driver_backend_plugin_selection.spl`. Reverting exactly those three files to
`origin/main` and re-running the hello-world `native-build` **still exits 132**,
so this is pre-existing on `origin/main`, not a regression from that lane.

## Why it blocks the goal chain

`--stop-after-stage2` fails as `stage2 native-build failed (exit 2)`; the Stage 2
sanity log records the same crash as
`candidate_frontend_smoke: hello-world-positional-build failed (raw rc=132)`
(`.simple/storage/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`).
With no admitted Stage 2 there is no Stage 3/Stage 4, so no self-hosted CLI can
be deployed, and `scripts/os/build-cortex-m-policy-objects.shs` cannot emit the
`access_policy` / `scalar_parser_fs_policy` objects the SimpleOS Cortex-M image
links against.

Note this area is under active repair upstream — 60 stage2-related commits landed
on `main` in the three days before this record, including
`1fc32815076 fix(frontend): keep flat-AST pool owners alive across the transient parse scope`
and `dd41c12bafb fix(seed): bind or-pattern match arms per alternative, not from the first one`.
Re-check this record against a newer `main` before investing in it.

## Unblock condition

A `native-build` of the three-line hello world above exits 0 on this host.
**Met 2026-09-26** on both backends (see Resolution). Not yet re-verified:
a full `--stop-after-stage2` run; the Stage-2 entry
(`app.cli.bootstrap_main` + `SIMPLE_BOOTSTRAP=1`) routes through
`bootstrap_compile_context_to_native_local`, which the interpreted worker still
resolves to the stub — re-run the phase-1 script and read its verdict rather
than assuming this fix covers it.

Do **not** "fix" this by silencing the bootstrap-flat warning — it is not the
cause (proved above), and it exists to stop a bootstrap-flat count being cited as
a clean tree
(`doc/08_tracking/bug/stage3_clean_baseline_is_bootstrap_flat_artifact_2026-08-01.md`).

## Reproduction artifacts

- `gdb` transcript, phase log, and the three `rc=132` runs were captured under
  the session scratchpad; the commands above reproduce them from a clean state.
- Related SIGILL family (different host/arch, same `ud2`-in-compiled-artifact
  shape): `doc/08_tracking/bug/seed_compiled_fixture_sigill_2026-09-15.md`.
