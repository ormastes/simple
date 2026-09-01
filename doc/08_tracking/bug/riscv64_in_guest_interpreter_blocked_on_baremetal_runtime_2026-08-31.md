# riscv64 in-guest Simple interpreter blocked on 43 missing baremetal `rt_*` symbols

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
error limit, not the size of the gap.** Reading it as "20 symbols to port" is a
trap — but so is the opposite error, which this record made on its first pass
and which is corrected here.

### The measurement, and the correction

Three numbers, only one of which is the answer:

| measurement | value | what it actually is |
|---|---|---|
| `ld.lld` errors in `kernel-build.log` | 20 | lld's default `--error-limit`. A floor, nothing more. |
| compiler's freestanding precheck | 405 | static, pre-`--gc-sections` |
| `nm` over emitted objects, undefined minus defined | 390 | static upper bound — **not the answer** |
| **replayed link, `--gc-sections` from the real entry, `--error-limit=0`** | **43** | **the true link-blocking set** |

The first version of this record cited 390 and concluded "porting is a project,
not a step." **That was wrong, and the error is worth naming**: 390 counts every
`rt_*` referenced anywhere in the 498 emitted objects, with no reachability
pruning. The link that actually runs applies `--gc-sections` from the entry, so
most of those references are in code the linker discards.

The correct measurement replays the real link over the build's own object
directory:

```
ld.lld -T examples/09_embedded/simple_os/arch/riscv64/linker.ld \
  --gc-sections --error-limit=0 --allow-multiple-definition \
  -e examples__09_embedded__simple_os__arch__riscv64__interpreter_hello_entry__spl_start \
  -o /tmp/probe.elf .simple/native-objects-<id>/*.o
```

Two things make this replay valid where earlier attempts were not, both worth
recording because each silently produced a wrong number:

* **The entry must be the MANGLED symbol.** Passing `-e spl_start` finds
  nothing, so `--gc-sections` discards the entire graph and the link reports
  **0** undefined — a vacuous green that looks like success.
* **`.inc.o` objects must be INCLUDED.** They are `#include`d fragments that
  also get compiled standalone by boot autodiscovery, so they duplicate symbols
  (`--allow-multiple-definition` absorbs that) — but they are also where PR
  #179's ~30 ported symbols actually live. Excluding them reports **65**
  instead of 43, double-counting symbols the tree already has.

### The real gap: 43 symbols

| bucket | n | symbols |
|---|---|---|
| file | 7 | `rt_file_exists`, `_probe_begin`, `_probe_end`, `rt_file_is_regular_no_follow`, `rt_file_read_text_rv`, `rt_file_remove`, `rt_file_write_text` |
| diagnostics / print | 8 | `rt_print_value`, `rt_println_value`, `rt_eprint_value`, `rt_panic`, `rt_function_not_found`, `rt_unwrap_or_trap`, `rt_is_debug_mode_enabled`, `rt_platform_name` |
| dict | 4 | `rt_dict_new`, `rt_dict_keys`, `rt_dict_values`, `rt_dict_contains` |
| transient heap | 4 | `rt_transient_array_scope_{begin,end,pause}`, `rt_transient_heap_promote` |
| env | 4 | `rt_env_{get,get_i64,set,remove}` |
| array / collection | 8 | `rt_array_copy`, `rt_array_extend_i64`, `rt_array_free`, `rt_push`, `rt_pop`, `rt_clear`, `rt_sort`, `rt_index_of`, `rt_collection_remove` |
| value / convert | 5 | `rt_value_as_int`, `rt_value_as_float`, `rt_value_float`, `rt_string_to_float`, `rt_raw_i64_to_string` |
| time | 2 | `rt_time_now_unix_micros`, `rt_time_now_monotonic_ms` |

The full list is committed as
`riscv64_interpreter_missing_rt_symbols_2026-08-31.txt`.

`rt_unwrap_or_trap` is in the set — the exact symbol behind the
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18` NULL-GOT
SIGSEGV. That is why this lane fails at link rather than being coerced into
linking: a green link here would reproduce that incident.

## Why this was not ported in-session

**Not because it is too large — because the session ran out of build cycles.**
43 symbols is roughly 1.4x PR #179's own port (~30 symbols, +712 lines in
`baremetal_runtime_core.inc.c`), so this is a #179-sized step, not a project.
The earlier "order of magnitude larger" framing was an artifact of the 390
miscount and is retracted.

What makes it more than an afternoon: each build-and-verify cycle on this host
is ~15 minutes, the ports must follow #179's load-bearing constraint —
**closure runtime ports must use the I32 codegen ABI**, per its commit title —
and roughly a third of the set (`rt_file_*`, `rt_env_*`, `rt_time_*`) needs
*honest* freestanding semantics rather than pass-throughs: a file probe that
truthfully reports "not present", a monotonic clock off the RISC-V `time` CSR.
Those must not be nil stubs; a nil stub here is the failure mode the whole lane
exists to detect.

Explicitly NOT done, and why:
* `SIMPLE_ALLOW_STUB_FALLBACK` / `SIMPLE_ALLOW_UNRESOLVED_RUNTIME` — never set.
  Either would produce a linking image that faults at runtime, the silent-lie
  class this lane exists to prevent.
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

The measurement the previous version of this record listed as "next step" is
**done** — the answer is 43, and the list is committed. The remaining work is
the port itself:

1. Port the 43 symbols into
   `examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c`
   following PR #179's pattern and its I32 codegen-ABI constraint. Start with
   the 21 pure-computation ones (dict, array/collection, value/convert) — they
   have no host dependency and unblock the largest share of the graph.
2. Give the 13 host-surface ones (`rt_file_*`, `rt_env_*`, `rt_time_*`) honest
   freestanding semantics, never nil stubs.
3. Rebuild and run the gate. It is already wired end to end and its evaluator is
   proven, so the first linking image produces a real verdict with no further
   gate work.

Closure reduction is no longer worth doing first: at 43 symbols the port is
cheaper than restructuring the entry to feed the interpreter a pre-lowered HIR
fixture, and the full-frontend path is the one that matches what
`simpleos_interpret_file` actually does.

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

---

## 2026-08-31 — the 44-symbol link blocker is CLOSED; two later defects now visible

**Status: the blocker this record was opened for is resolved.** Both riscv64
in-guest kernels build and link with **zero undefined symbols**, and the
interpreter guest now boots under real OpenSBI `-bios fw_payload` and reaches
its entry. What the lane reported before —

    ERROR — nothing was checked: interpreter kernel build failed:
    ld.lld: error: too many errors emitted

— no longer happens. `build-simpleos-riscv64-interpreter-kernel.shs` reports:

    PASS — riscv64 interpreter + build-and-run kernels built by the RUST SEED

### What was measured

The 43 symbols listed in `riscv64_interpreter_missing_rt_symbols_2026-08-31.txt`
were confirmed on the real link, all ported into
`arch/riscv64/boot/baremetal_runtime_core.inc.c` as a fourth tranche. Resolving
them surfaced exactly **one** further symbol, `spl_wffi_call_i64` (the weak-FFI
integer call thunk, emitted by `compiler.blocks.sugar_registry.apply_rule_ast`),
also ported. **44 total.** `nm` on both linked ELFs shows every one as a strong
`T`; `rt_unwrap_or_trap` is a 60-byte real trap body, not an 8-byte weak stub.

A cross-check worth recording, because it wasted time twice: replaying the link
out of a preserved `.simple/native-objects-*` directory reports **1 undefined
symbol (`spl_start`) regardless of the tree's true state**. Those directories do
not contain the entry-closure object, so `--gc-sections` rooted at `_start`
finds `spl_start` undefined, collects the entire module graph as dead, and never
reports the `rt_*` references inside it. That is a third member of the
vacuous-green family already noted for `-e spl_start`. **The real build script is
the only honest measurement.**

### Defect A — in-guest parser makes no forward progress on a StringLit

The interpreter guest boots, prints its banner, and runs the real frontend
in-guest. It then fails identically every time:

    [interp] lowering hello-world source through the real frontend
    [stderr] [parser-module] decl:start i=0 kind=3 text= line=3 col=3
    [parser_error] line 3:3: parser made no forward progress at this token (StringLit ''); aborting module parse
    [parser_error_ctx] path  kind 3 text ''

The token is correctly classified (`kind=3`, StringLit) at the right position
(line 3 col 3), but its **text is empty** — so this is token-text extraction in
the freestanding lexer, not a grammar problem. The guest then resets and repeats;
the transcript holds 3,044 identical cycles in ~21 MB.

### Defect B — the OpenSBI payload wrap is not rebuilt per row, so both rows boot the SAME image

`buildrun/kernel.elf` links, and the build script's symbol check confirms
`buildrun_sanity_row` is present in it. But its serial transcript prints the
**`[interp]`** banners, never the `[buildrun]` ones that
`buildrun_sanity_entry.spl` actually emits. The gate reports this honestly:

    ERROR — nothing was checked: the build-and-run guest never reached its
    entry — no boot rungs on serial

Root-caused: the buildrun kernel is NOT at fault. `nm` on
`buildrun/kernel.elf` shows exactly one row symbol —
`...buildrun_sanity_entry__buildrun_sanity_row` — with `interpreter_hello_row`
ABSENT and a single `spl_start`, so there is no entry-closure pollution and the
right entry is linked. The two `kernel.Image` files also differ
(`79829008…` vs `744a0979…`).

The defect is in the OpenSBI wrap step: the two payloads are **byte-identical**
(`b214f3f2652786909e113b915521aff1` for both `interp-fw_payload.bin` and
`buildrun-fw_payload.bin`), and `buildrun-opensbi-build.log` reads

    make: Nothing to be done for 'all'.

The OpenSBI `make` treats its output as up to date across rows because nothing
in its dependency set changed — `FW_PAYLOAD_PATH` pointing at a different kernel
Image is not something make sees. So the buildrun row boots the INTERPRETER
payload, which is exactly why `[interp]` banners appear in the buildrun
transcript. The fix is to force a rebuild (or clean the payload output) between
rows; a row symbol being present in the ELF is not evidence that row's image is
what was booted.

This is why the gate's verdict is still ERROR rather than FAIL: the interpreter
row DID reach its entry (it passes the same precondition at line 486), and the
run stops at the buildrun boot-rung check.

### Defect A is NOT caused by the port's behavioural choices

Checked explicitly, because this change chose `rt_env_get` -> nil,
`rt_env_get_i64` -> default and `rt_is_debug_mode_enabled` -> 0, and those now
define every env/config gate inside the guest. Token text is stored by
`lexer_core_cur_text_set` (`10.frontend/core/_Ast/module_state.spl:351`), a
plain string store; there is no `env_get` / `is_debug_mode` / `getenv` read
anywhere under `10.frontend`'s lexer path. The empty StringLit text is therefore
not a consequence of those answers. Recorded because there is no pre-port
baseline to compare against — the image never linked before — so attribution had
to be established by inspection rather than by bisection.

Neither defect is a runtime-symbol gap, and neither is fixed by this change.
