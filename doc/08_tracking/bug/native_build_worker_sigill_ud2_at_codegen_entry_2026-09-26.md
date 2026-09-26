# `native-build` worker dies with SIGILL (`ud2`) at codegen entry, on every build

- **Filed:** 2026-09-26
- **Status:** OPEN — blocks Stage 2, therefore phase 1 `--stop-after-stage2`, the
  local-temp MCP redeploy, and every Cortex-M policy-object build
- **Area:** `80.driver` diagnostics + JIT codegen (cranelift and llvm lanes alike)
- **Host:** yoon-note, x86_64-unknown-linux-gnu, 7 GiB RAM
- **Seed:** built 2026-09-26 09:02 from `03553bcb5f6` (= `origin/main` `49389cb10f3`
  plus 13 unrelated Cortex-M files), `Simple Language v1.0.0-rc.1`

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

Next step for whoever picks this up: the fault is at codegen entry, so bisect
there rather than in the diagnostics. Useful probes, cheapest first — set
`SIMPLE_COMPILER_PHASE_PROFILE=1` to get `[BOOTSTRAP-PHASE]` deltas across the
mir->codegen boundary and find the last phase marker before the trap; then run
the worker generation binary under `gdb` with `set follow-fork-mode child` and
break on the codegen entry point to get a backtrace with named frames instead of
two anonymous JIT addresses.

Do **not** "fix" this by silencing the bootstrap-flat warning — it is not the
cause (proved above), and it exists to stop a bootstrap-flat count being cited as
a clean tree
(`doc/08_tracking/bug/stage3_clean_baseline_is_bootstrap_flat_artifact_2026-08-01.md`).

## Reproduction artifacts

- `gdb` transcript, phase log, and the three `rc=132` runs were captured under
  the session scratchpad; the commands above reproduce them from a clean state.
- Related SIGILL family (different host/arch, same `ud2`-in-compiled-artifact
  shape): `doc/08_tracking/bug/seed_compiled_fixture_sigill_2026-09-15.md`.
