# riscv64 in-guest Simple interpreter blocked on ~390 missing baremetal `rt_*` symbols

Date: 2026-08-31
Status: OPEN — lane landed, honestly RED (gate exits 2, `ERROR — nothing was checked`)
Base: `fix/simpleos-riscv64-components` (PR #179, `ed610b469e2`)
Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`

## Goal row this blocks

"Simple running INSIDE SimpleOS on riscv64 — hello world in the INTERPRETER,
plus build-and-run sanity." Both rows are wired end to end and neither can be
measured in-guest yet, because the guest image does not link.

## What was built (all landed, all reusable)

The lane deliberately does NOT construct a second boot chain. It parameterizes
the proven riscv64 OpenSBI `fw_payload` chain already used by
`check-simpleos-riscv64-hello-world-in-guest-opensbi.shs` and the PR #179
toolchain-components lane: real OpenSBI v1.4 (`a2b255b8891...`, the same pin as
its siblings) built with the guest Image embedded and handed to QEMU as `-bios`
only — never `-kernel`, never `isa-debug-exit`, with the assembled argv
self-checked for both before any VM starts.

* `examples/09_embedded/simple_os/arch/riscv64/interpreter_hello_entry.spl` —
  row 1. Drives the REAL interpreter (`InterpreterBackendImpl.interpret_hir_module`,
  the same call `src/app/simpleos_tool/focused_pipeline.spl` drives on a hosted
  build) over hello-world source text. The interpreted program's OWN `print`
  puts the marker on serial; nothing in the entry prints that line.
* `examples/09_embedded/simple_os/arch/riscv64/buildrun_sanity_entry.spl` —
  row 2. Frontend + real `MirLowering.lower_module` (the BUILD half) then runs
  the program, which must compute `40 + 2 == 42`.
* `scripts/os/build-simpleos-riscv64-interpreter-kernel.shs` — one kernel per
  row (a combined `--entry-closure` union is what leaves ~500 `rt_*` undefined,
  per the components lane's own header). Generates the per-run NONCE into
  `build/os/generated/rv64_interp_nonce.spl` and refuses an image lacking the
  row symbol, the interpreter symbol, or the nonce bytes.
* `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs` — the
  gate. Repo verdict convention, nonce-anchored (never a fixed banner),
  `nm`-based weak-nil-stub check before boot, FATAL 23-fixture `--selftest`
  including banner-only must-FAIL rows for both rows.

## The blocker, as measured

`native-build --target riscv64gc-unknown-none-elf` compiles the closure and then
fails at link:

```
ld.lld: error: undefined symbol: rt_dict_keys
>>> referenced by simple_module
>>>   .../mod_316.o:(compiler__backend__backend__env__Environment_dot_snapshot_locals)
>>>   .../mod_327.o:(compiler__backend__backend__interpreter_calls__InterpreterBackendImpl_dot_call_closure)
>>> referenced 37 more times
ld.lld: error: too many errors emitted, stopping now (use --error-limit=0 to see all errors)
```

**The log names exactly 20 undefined symbols, and that number is lld's default
error limit, not the size of the gap.** Reading it as "20 symbols to port" is
the trap here. Two independent measurements agree on the real magnitude:

| measurement | value |
|---|---|
| compiler's own freestanding precheck (`kernel-build.log`) | `405 unexpected symbol(s)` |
| `nm` over the emitted objects, undefined minus defined minus what `arch/riscv64/boot/` defines | **390** |

The 390-symbol list is committed alongside this record as
`riscv64_interpreter_missing_rt_symbols_2026-08-31.txt`. Bucketed by subsystem:

| bucket | count | bucket | count |
|---|---|---|---|
| `rt_file_*` | 30 | `rt_array_*` | 20 |
| `rt_time_*` | 22 | `rt_math_*` | 19 |
| `rt_process_*` | 18 | `rt_string_*` | 11 |
| `rt_text_*` | 7 | `rt_env_*` | 7 |
| `rt_dict_*` | 5 | `rt_value_*` | 5 |
| `rt_atomic_*` | 3 | `rt_any_*`, `rt_thread_*`, `rt_browser_*` | 2 each |
| remainder (unprefixed / long tail) | ~237 | | |

Notably `rt_unwrap_or_trap` is in the set — the exact symbol behind the
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18` SIGSEGV, where
a tolerated undefined symbol became a NULL GOT slot at runtime. That is why this
lane fails at link rather than being coerced into linking: a green link here
would reproduce that incident.

## Why this was not ported in-session

PR #179 ported ~30 `rt_*` symbols to the riscv64 baremetal runtime in +712 lines
of `baremetal_runtime_core.inc.c`, under the constraint its commit title records
— **closure runtime ports must use the I32 codegen ABI**. The gap here is an
order of magnitude larger (~390 vs ~30) and spans subsystems a freestanding
S-mode image has no business implementing wholesale (`rt_process_*`,
`rt_file_*`, `rt_time_*`, `rt_browser_*`). Porting it is a project, not a step.

Explicitly NOT done, and why:
* `SIMPLE_ALLOW_STUB_FALLBACK` / `SIMPLE_ALLOW_UNRESOLVED_RUNTIME` — never set.
  Either one would produce a linking image that faults at runtime, which is the
  silent-lie class this whole lane exists to prevent.
* Weakening the gate to allowlist "probably dead" undefined symbols — the
  weak-nil-stub check exists precisely because a clean link is not evidence.

## The U-mode question, settled

The prior note described the gap as "riscv64 needs a U-mode exec lane —
scheduler + ELF loader closure". **That is stale.** riscv64 already has:

* a kernel-side U-mode ELF loader with Sv39 page-table construction —
  `examples/09_embedded/simple_os/arch/riscv64/boot/rv64_fs_exec_loader.inc.c`
  (`rv64_pt_map_4k`, `rv64_fs_map_user_elf`), plus FAT32/virtio-blk media in
  `rv64_fs_exec_media.inc.c`;
* an `sret`-to-U-mode path, an `stvec` trap vector with `sscratch` swap, and
  `scause`-decoded write/exit `ecall` handling;
* a scheduler and `_rv64_enter_user` in `arch/riscv64/entry.spl`.

What actually blocks U-mode is neither missing: the public execution entry
**`rt_riscv_fs_exec_run()` deliberately fails closed, returning `-13`**, pending
"an authority token bound to digest, mount/file identity, and content
generation" from a canonical loader that does not exist yet. Grep confirms the
authenticated path is referenced only in that prose — there is no such code.

Routing around that fail-closed to manufacture a U-mode row would be defeating a
security control, not producing evidence, so this lane runs in S-mode like every
other in-guest row in the tree (x86_64 PR #177, aarch64 PR #175, riscv64
components PR #179) and says so in every header.

## Current honest verdict

```
ERROR — nothing was checked: interpreter kernel build failed: ld.lld: error: too many errors emitted, stopping now (use --error-limit=0 to see all errors)  build-riscv64-interpreter-kernel: ERROR — native-build failed for interp (rc=1), log: .../build/os/riscv64_interp/interp/kernel-build.log
```

Exit 2. This is the correct classification, not a FAIL: the guest never ran, so
no row was evaluated. `--selftest` is independently green —
`PASS — 23 selftest fixture(s) checked, serial evaluator, nonce anchoring,
weak-nil-stub detector and argv guard all discriminate` — so the evaluator is
known-good and will report truthfully the moment an image links.

## Next step, concretely

Get the exact link-blocking set (not the static-reference upper bound) by
re-linking with `--error-limit=0`, then port that set into
`baremetal_runtime_core.inc.c` following PR #179's pattern and its I32
codegen-ABI constraint. Reducing the closure is the cheaper lever worth trying
first: the entry currently pulls `parse_and_build_module` + full desugar +
`HirLowering`; a probe importing only `InterpreterBackendImpl` and the HIR types
would show whether the frontend or the interpreter is the heavy half, and
whether a pre-lowered HIR fixture lets row 1 land far sooner than row 2.

## Two defects found and fixed in this lane's own scripts

Recorded because both are the repo's own documented hazards, caught here by the
gate's fixtures rather than by review:

1. **`nm` type-column indexing.** The weak-nil-stub detector matched on `$1`,
   but `nm` prints `ADDR TYPE NAME` for defined symbols and `<blank> U NAME` for
   undefined ones — the type is `$(NF-1)` in both shapes. Indexing on `$1`
   silently matched nothing for defined symbols and let a real `WEAK` stub
   through. Caught by this gate's own must-FAIL fixture, which builds a genuine
   weak-symbol object with `cc` and probes it with the real detector.
2. **`set -e` swallowing the build diagnostic.** In the kernel builder, a
   failing `native-build` under `set -e` aborted the script AT the invocation,
   so the `rc=$?` line and its `tail`-the-log diagnostic never ran. A real link
   failure surfaced as a silent exit 1 with empty stderr — indistinguishable
   from an environment glitch. Fixed with an explicit `set +e` / `rc=$?` /
   `set -e` window around the invocation.

A third, in the gate: a multi-line log excerpt embedded in the `ERROR` verdict
pushed the verdict off the last line of stdout. Flattened with `tr`.
