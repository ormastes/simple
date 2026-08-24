# Design: MCP server running inside SimpleOS under QEMU

- **Date:** 2026-08-23
- **Status:** DESIGN, with P8 AND P9 BUILT AND PROVEN (see the status updates below).
  The end-to-end capability does NOT exist: no MCP server has run inside a
  SimpleOS guest, and no gate reports a pass for it. What is proven is two
  prerequisites — the guest byte channel in BOTH directions, evidenced by
  nonce-matched serial logs from real-firmware boots. P10 is now inventoried:
  151 declared externs, 11 present, 140 missing, of which ~90 are mechanical.
- **Scope:** aarch64 (`aarch64-unknown-simpleos`) under QEMU `virt` with real
  firmware. x86_64 and riscv64 are out of scope for milestone 1 — see
  Prerequisites.
- **Context:** There is no MCP-on-SimpleOS artifact anywhere in this repo or in
  any of the 223 GitHub remote branches. This is net-new work.

## STATUS UPDATE 2026-08-24 (4) — ROUTE A STEP 2 DONE: THE MCP SERVER RUNS IN THE GUEST

**The MCP module graph is built into the aarch64 kernel, entered from the boot
path under real firmware, and runs its startup and serve loop to a clean
`exit(0)` on EOF — with no trap fired.** It has NOT answered a request; the gate
lane feeds no input. That is step 3.

`src/os/kernel/boot/limine_boot_aarch64.spl` now imports
`app.mcp.main.{main as mcp_server_main}` and calls it after the P10 marker —
the same discipline as the P8/P9/P10 probes, so nothing beneath it can turn the
boot gate's PASS into a FAIL.

### The undeclared-symbol axis, finally measured: 16, and exactly ONE layer deep

This doc has warned since the P10 inventory that the declared surface "is not
the total ABI bill". The number was never known. It is now:

| | count |
|---|---|
| declared externs in the `src/app/mcp/main.spl` closure | 150 |
| **undeclared, codegen-emitted symbols** | **16** |
| of those 16 that appear anywhere in the declared 150 | **0** |
| **total ABI bill for the MCP graph on Route A** | **166** |

The 16: `rt_array_copy`, `rt_array_sort`, `rt_dict_new`, `rt_file_read_text_rv`,
`rt_file_remove`, `rt_get_args`, `rt_index_of`, `rt_string_char_at`,
`rt_string_replace`, `rt_string_rfind`, `rt_string_to_float`,
`rt_string_to_int_lenient`, `rt_string_to_lower`, `rt_string_to_upper`,
`rt_text_find`, `rt_value_as_float`.

They are emitted by codegen for built-in method syntax (`.to_upper()`,
`.find()`, `.sort()`, dict literals), which is why **no extern-based inventory
could ever have seen them** — including this doc's own. They surfaced only when
the graph was compiled for the target, exactly as predicted.

**Depth measured, not assumed:** defining the 16 closes the link (rc 0). A
second iteration produced **zero** new undefined symbols. There is no third
layer.

**One favourable difference from the `rt_unwrap_or_trap` NULL-GOT class**
(`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`): on this
lane the link is **fail-CLOSED**. `ld.lld` reported
`undefined symbol: rt_text_find` and friends and exited non-zero. It did not
silently emit a null GOT slot to fault at first call. The freestanding link
names the gap instead of deferring it to runtime.

### What was implemented vs trapped

15 of the 16 are NAMED TRAPS, on the same terms as the 56 — link closure, never
a returned value. They are not equal in difficulty and the buckets say so: 12
string/array entries are pure computation and are step 3's real work;
`rt_dict_new` needs a heap kind this runtime does not have (it knows
`RT_HEAP_STRING`/`ARRAY`/`TUPLE`/`ENUM` only); 2 filesystem entries need the
same absent subsystem as the 29.

`rt_get_args` was **implemented for real**, not trapped. It is codegen's twin of
the already-real `sys_get_args`, and a freestanding guest genuinely was never
handed an argv, so an empty `[text]` is the truth here, not a stub. It was
promoted only after a live boot proved it is the first symbol `main()` reaches
(`src/app/mcp/main.spl:345` calls `mcp_get_cli_args()` on its first line).

### The live evidence

First boot, with all 16 trapped — the graph is entered and stops loudly, by
name, on the easiest symbol in the set:

```
[BOOT] SIMPLEOS-AARCH64-LIMINE-P10-ABI-PINNED symbols=157
[BOOT] SIMPLEOS-AARCH64-LIMINE-MCP-GRAPH-ENTERING
[TRAP] simple runtime: unimplemented entrypoint `rt_get_args` was called.
[TRAP] This is a NAMED TRAP stub, not an implementation. Core parked.
```

That transcript is also the **first time a trap has ever been executed** on this
lane; until now `rt_trap_unimplemented`'s UART path was inherited and
unexercised. It works: named, loud, not a silent nil and not a SEGV.

Second boot, with `rt_get_args` real — **no trap at all**:

```
[BOOT] SIMPLEOS-AARCH64-LIMINE-P10-ABI-PINNED symbols=157
[BOOT] SIMPLEOS-AARCH64-LIMINE-MCP-GRAPH-ENTERING
[EXIT] rt_exit(0) - no process model in this lane; core parked.
```

`main()` ran its whole startup, reached the serve loop, called
`_mcp_read_message()`, got EOF (`-serial file:` is TX-only, so no byte can
arrive), and took the `msg == ""` branch to `exit(0)`
(`src/app/mcp/main.spl:408-411`). **This empirically confirms the prediction in
update (2)**: the startup and serve-loop path touches only `get_args`,
`env_get`, `exit`, `stderr_write`/`flush`, `stdin_read_char` and `print_raw`,
all real. The 15 remaining traps are reachable only once a request arrives.

### Measurements

| | step 1 | step 2 |
|---|---|---|
| modules compiled | 9 | **68** |
| image | 133,664 B | **955,712 B** |
| defined symbols | 361 | **3,387** |
| undefined in linked `kernel.elf` | 0 | **0** |
| keepalive marker | `symbols=141` | **`symbols=157`** |
| `[BOOT]` markers in transcript | 66 | **67** |
| serial lines | 95 | 98 |

**No regression to the documented build recipe.** The recipe in
`aarch64_limine_kernel_has_no_builder_script_2026-08-23.md` carries no
`--source` flags; it still builds, and its output is **byte-identical** to a
build with `--source src/app --source src/lib --source src/compiler`. The
default source roots already cover the graph.

**Verdicts, rc read into a variable on the following line:**

```
PASS — 4 boot-stage marker(s) checked, EDK2/AAVMF pflash real-firmware aarch64
boot verified via BOOTAA64.EFI on a FAT ESP (no -kernel, no isa-debug-exit),
98 serial line(s) captured                                            rc 0

PASS — 10 marker(s) checked in each of 2 boot paths, unified arm64 early-boot
verified under EDK2/AAVMF pflash real firmware via Limine BOOTAA64.EFI
`protocol: linux` (no -kernel, no isa-debug-exit, self-relocation exercised)
and unchanged under legacy -kernel                                    rc 0
```

`scripts/check/check-no-unresolved-runtime-symbols.shs` — the gate that exists
for exactly this failure class — could **not** run here:
`ERROR — nothing was checked (selftest failed)`, rc 2. It is Linux-only, deriving
the platform-library set from `ldd` (`:133`), which macOS does not have. That is
an environmental ERROR, correctly not a pass. The substance was measured
directly instead: `llvm-nm -u` on the linked artifact reports **0 undefined**,
and the link is fail-closed as described above.

### Step 3 is now a bounded, named list

The blocker is no longer structural discovery. It is:

1. Implement the **12 string/array primitives** for real (`rt_text_find` first —
   it is reached from `app__mcp__main_lazy_json___find_json_value_start`, i.e.
   JSON parsing, which is on the `initialize` path). Pure computation, the same
   class as the 19 text/utf8 entries already done.
2. Feed the request **during** the guest's polling window (`-serial stdio`, not
   `-serial file:`) — the pacing finding from P8, still unaddressed.
3. `rt_dict_new` only if the `initialize` path actually reaches it; that one is
   a new heap kind, not a primitive.

### Not verified by this pass

- **No MCP request was answered and no round trip was attempted.** The server
  reached EOF because nothing was fed to it. Step 3 was deliberately not started.
- Whether the `initialize` path reaches `rt_dict_new` is **unknown** — it will
  be answered by the first real request, not by reading code.
- Route B untouched and still P6-blocked. All of this is Route A's bill.
- No board run.

## STATUS UPDATE 2026-08-24 (3) — ROUTE A STEP 1 DONE: THE 56 ARE TRAPPED, LINK CLOSURE REACHED

All 56 are now NAMED TRAPS in
`examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`, via
`SPL_P10_TRAP`, the shape the 41 SIMD kernels already used. **Link closure, not
implementation** — every one prints its own symbol over PL011 and parks the
core. No value is returned by any of them; that would be the silent-nil class
(`unregistered_extern_silent_nil_2026-08-01`, and the `rt_unwrap_or_trap`
NULL-GOT SEGV). Step 2 was deliberately NOT attempted.

**Baseline reproduced first**, so the delta is attributable. The documented
recipe (`aarch64_limine_kernel_has_no_builder_script_2026-08-23.md`) rebuilt the
tracked `kernel.elf` **byte-identically** — 123,912 bytes, identical defined-symbol
set, 0 undefined — before a line was changed.

**Measured after:**

| | before | after |
|---|---|---|
| declared externs of the `src/app/mcp/main.spl` closure still missing | 56 | **0** |
| defined T-symbols in `kernel.elf` | 305 | **361** (+56, exactly) |
| undefined symbols in `kernel.elf` | 0 | **0** |
| image | 123,912 B | 133,664 B |
| boot marker | `symbols=85` | **`symbols=141`** (85 + 56) |

All 56 survive `--gc-sections`: **0 GC'd**, because they were added to the
`g_p10_keepalive` table in the same change. The marker is computed from
`sizeof(g_p10_keepalive)` at runtime, so `limine_boot_aarch64.spl` needed no
edit. **No gate asserts the literal `symbols=85`** — verified by grep; the only
occurrence in the tree is the emitter at `limine_boot_aarch64.spl:555`, and the
marker is printed after every marker the boot gate greps. So no assertion was
updated, and none was silently weakened.

**No runtime regression from trapping.** The full serial transcript diffs
against the pre-change boot in exactly three places, all explained by a
9,752-byte-larger image: memory-map regions 6/7 shift by 8,192 B (two 4 KiB
pages), PMM `free_pages` 120,349 -> 120,347 (the same two pages), and the
`symbols=` line. **Zero `[TRAP]` lines** in the 95-line capture, all 66 `[BOOT]`
markers present. Nothing the kernel executes reaches a trap — as predicted, the
first thing any of them can interrupt is a `tools/call`.

**Verdicts, rc read into a variable on the following line:**

```
PASS — 4 boot-stage marker(s) checked, EDK2/AAVMF pflash real-firmware aarch64
boot verified via BOOTAA64.EFI on a FAT ESP (no -kernel, no isa-debug-exit),
95 serial line(s) captured                                            rc 0

PASS — 10 marker(s) checked in each of 2 boot paths, unified arm64 early-boot
verified under EDK2/AAVMF pflash real firmware via Limine BOOTAA64.EFI
`protocol: linux` (no -kernel, no isa-debug-exit, self-relocation exercised)
and unchanged under legacy -kernel                                    rc 0
```

### What "0 undefined" does and does NOT prove

It proves the **declared** surface is closed: 150 of 150. It proves nothing
about the total ABI bill, because **this kernel does not contain the MCP module
graph** — step 2 is what builds it in. The undeclared axis (codegen-emitted
runtime calls no `extern` declares, the `rt_unwrap_or_trap` NULL-GOT class) can
only surface there, and remains entirely unmeasured. A linked static ELF trivially
has 0 undefined symbols; that number is evidence only alongside the +56 defined
count and the moved marker.

The compiler's own freestanding precheck reported `3 unexpected symbol(s)` /
`2 candidate symbol(s) deferred to linker` — **unchanged from baseline**, so this
change neither added to nor cleared that pre-existing set.

### Not verified by this pass

- Step 2 not attempted, by instruction.
- Guest stdin RX still not re-proven (`[STDIN-PROBE] no-data`, the documented
  TX-only `-serial file:` expectation).
- No trap was ever *executed*; that the trap text reaches the UART is inherited
  from `rt_trap_unimplemented`, unexercised here.
- Route B untouched and still P6-blocked. These 56 are Route A's bill only —
  see the update below.

## STATUS UPDATE 2026-08-24 (2) — THE 56 ARE ON A DIFFERENT LINK SET THAN M1'S ROUTE

Independent verification pass. The 56 figure below is **confirmed exactly**, by
re-derivation rather than by trusting this doc. But the same pass turned up a
split this doc does not reconcile, and anyone who reads "56 externs remain"
without it will implement them against the wrong link set.

### The route split — TWO routes, disjoint C link sets, neither blessed

Read out of the build scripts, not inferred:

| | Route A — kernel-embedded | Route B — guest process (`/usr/bin/simple mcp`) |
|---|---|---|
| C link set | `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c` — the directory holds exactly ONE `.c`, so this is the complete set | `src/os/libc` (~40 `.c`, incl. `simpleos_fs.c`, `simpleos_process.c`, `simpleos_socket.c`, `simpleos_fork.c`) + `libsimple_runtime.a` cross-built from **11** `src/runtime` files (`simpleos-sysroot-aarch64.shs:110-114`) |
| built by | the same bootstrap `native-build` that already produces `kernel.elf` | `scripts/os/simpleos-native-build-aarch64.shs` |
| status | boots today, gate-green | **P6-blocked** |

**`freestanding_runtime.c` appears NOWHERE in Route B's path.** Route B resolves
`rt_file_*` / `rt_process_*` / `rt_mmap` from the cross-built `src/runtime` C
instead. So **the 56 counted below are Route A's bill, and §4.1's M1 — which
specifies `/usr/bin/simple mcp` reading fd0 — is Route B.** Route B's extern
bill is a *different, unmeasured* set; it can only be measured by actually
linking the payload, which P6 blocks.

This is stated, not resolved. Nothing in the tree says which route is intended,
and this pass did not establish it. Do not read the table as a recommendation.

### Measured reconciliation of the 56

- Transitive `use` closure of `src/app/mcp/main.spl`: **49 modules, 0
  unresolved, 150 distinct `extern fn`** — matches the figure below.
- `clang --target=aarch64-unknown-none-elf -ffreestanding -nostdlib -c` on
  `freestanding_runtime.c`: 227 defined globals, of which **94** are in the
  declared set. **150 − 94 = 56.** Delta against this doc: **zero.**
- 94 = **11 pre-existing + 83 implemented**; `sqrt` is the 84th and lies outside
  this closure, hence 94 not 95.
- `nm` on the linked `kernel.elf`: **85 of the 94 survive**; the 9 GC'd are
  exactly the predicted no-reference set (`rt_hash_text`, the five
  `rt_string_builder_*`, `rt_string_bytes`, `rt_string_len`,
  `rt_text_to_bytes`). `kernel.elf` has **0 undefined symbols**, and the boot
  marker `[BOOT] SIMPLEOS-AARCH64-LIMINE-P10-ABI-PINNED symbols=85` agrees.
- Bucketing note: this pass puts `rt_thread_sleep` with process (19) and time at
  2, where the table below splits process 18 / time+thread 3. Same 56 symbols.

### 53 of the 56 are INCIDENTAL to M1 — traced, not inferred

`main()`'s startup, serve loop, and `initialize` path touch only `get_args`,
`env_get`, `exit`, `stderr_write`/`stderr_flush`, `stdin_read_char`,
`print_raw`. All six are present in **both** the compiled object and
`kernel.elf`. `tools/list` is answered from a local static payload
(`_mcp_tools_list_payload`), pure text. The only `file_exists` consumer,
`_mcp_find_simple_binary`, is reachable **only from `tools/call`** —
`cli_passthrough.spl:21`, `dap_bridge.spl:147`,
`main_lazy_diag_tools.spl:137,261`, `main_lazy_query_tools.spl:335` — never from
startup or `initialize`.

So FS 29 + process 18 + mmap 4 + browser 2 = **53 are needed for LINK CLOSURE
ONLY**: a static freestanding link must resolve a symbol whose call site is
emitted even when it is never executed. The honest pattern for that already
exists in this lane — the 41 `rt_trap_unimplemented` SIMD traps. `rt_thread_sleep`
and the 2 `rt_time_*` are the only plausible serve-loop wants, and none of the
three is required for one round trip.

### Route A shortest path

1. Trap-body the remaining 56 for link closure, using the existing 41 SIMD traps
   as the pattern. Mechanical.
2. **UNTESTED.** Build an MCP-graph entry with the same bootstrap `native-build`
   that already produces `kernel.elf`, and call `main()` from the boot path after
   the existing markers. This is where the **undeclared-symbol axis** surfaces —
   the `rt_unwrap_or_trap` NULL-GOT SEGV class,
   `doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`.
   That cost is genuinely unestimated; step 1's 56 is not the total ABI bill.
3. Switch the gate from `-serial file:` to `-serial stdio` and feed the request
   **during** the guest's polling window, per the pacing finding recorded in the
   P8 update below.

Route A sidesteps P6, P7, and P11 entirely. Route B remains blocked on all
three: P6 (`doc/08_tracking/bug/admitted_stage2_builder_cannot_cross_build_simpleos_payload_2026-08-23.md`
— the only Stage-2-admitted builder is the bootstrap CLI, advertising none of
`--target` / `--runtime-bundle` / `--linker-script` / `--entry-closure`), P7
downstream of it, and P11 (`GUEST_WORKFLOW_READY=0`, hardcoded).

### Gate inventory note

`scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs` has **no
`PASS —`/`FAIL —`/`ERROR —` verdict-line emitter at all**, and it **boots
nothing**: it reports `simpleos_x86_64_wm_qemu_preflight_live_qemu=not-started-host-gate`
alongside `..._status=pass` and exits 0. A reader who sees rc 0 will assume a
boot happened; it did not. Observed, not changed — it belongs to another lane.

### NOT verified by this pass

- **No P6 build was attempted.** The aarch64 sysroot and the `simple-core`
  archive are absent on this host; nothing was built to test Route B.
- **Guest stdin RX was not re-proven.** The boot in this pass shows
  `[STDIN-PROBE] no-data`, the documented expectation for a TX-only
  `-serial file:` gate. P8's proof rests on the earlier nonce run, unreproduced
  here.
- A grep found 48 of the 56 named somewhere in `src/runtime` C. That figure is
  **indicative only** — it scanned all 103 non-vendor `src/runtime` `.c` files,
  whereas Route B links exactly **11** of them. The 8 mmap/file-lock symbols
  (`rt_mmap`, `rt_munmap`, `rt_madvise`, `rt_msync`, `rt_file_lock`,
  `rt_file_unlock`, `rt_file_mmap_read_bytes`, `rt_file_mmap_read_text`) are
  absent from `src/runtime` C **entirely**.
- The `freestanding_runtime.c` compile used this pass's own flags, not the lane's
  exact ones. The number is anchored by the `kernel.elf` cross-check (85 of 94
  present, 0 undefined), not by the compile alone.

## STATUS UPDATE 2026-08-24 — P10's MECHANICAL HALF IS BUILT (84 of 140)

The ~90 "mechanical" symbols the inventory below identified are implemented in
`examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c` and
present in a real, gate-passing `kernel.elf`. **P10's remainder is now 56.**
(84 = 83 symbols from the reproduced 139-missing set, plus `sqrt`, which is the
140th symbol of the recorded set and is absent from the closure reproduced
below. 140 - 84 = 56 either way.)

**Inventory reproduced first, independently.** A fresh transitive-`use` closure
of `src/app/mcp/main.spl` gives 49 modules / **150** declared externs, of which
exactly the **same 11** the table below names were already defined. The 1-symbol
gap against the recorded 151/140 is **`sqrt`**, which this closure never
reaches; it was implemented anyway (AArch64 `FSQRT` via `__builtin_sqrt`), so
the gap is closed rather than argued about.

**What was implemented, and how honestly.** The split is deliberate:

| bucket | n | outcome |
|---|---|---|
| text / utf8 / string-index | 19 | REAL implementations |
| `rt_simd_*` capability probes + `rt_simd_str_search` | 8 | REAL answers for this lane |
| `rt_simd_*` arithmetic / lane kernels | 41 | **NAMED TRAPS** |
| atomics / atexit / signal | 7 | real atomics; signals honestly absent |
| env / exit / args | 5 | honestly empty freestanding answers |
| stdio siblings of `print_raw` | 3 | REAL, out the same PL011 |
| `sqrt` | 1 | REAL |

The 41 SIMD kernels take `Vec4f`/`Vec8i`/... — **class** values whose native
layout this freestanding runtime cannot construct (it knows only
String/Array/Tuple/Enum), and whose only authority in the tree is a
field-bearing object (`interpreter_extern/simd.rs:619-636`). Fabricating a
vector would be silent numeric corruption, which
`src/compiler/70.backend/backend/simpleos_native_symbols.spl:158-163` already
forbids by name for exactly this family. They therefore get a **freestanding
`rt_trap_unimplemented`** — a libc-free twin of `runtime_native.c:11623` that
prints the symbol over the UART and parks the core. The capability probes
report **scalar / no accelerator**: not a claim about the CPU, a claim about
this lane, which ships no vector kernels — reporting NEON would route
`std.simd`'s dispatchers straight into those traps.

Two signature surprises worth recording: `rt_utf8_count_codepoints` /
`_validate` / `_find_invalid` take **`[i64]`, not `[u8]`**
(`src/lib/common/encoding/utf8.spl:14-16`), and `rt_bytes_to_text` is declared
**both ways** in the same closure (`[u8]` at `utf8.spl:18`, `[i64]` at
`width_index.spl:19`) — one C body satisfies both, because both are the same
RtArray-of-tagged-ints at the ABI.

**`--gc-sections` tax: ZERO of 86 written symbols, and that took work.** Nothing
in this kernel calls a P10 symbol (the MCP graph is not built in until P6/P11),
so without a root every one would have been discarded. A keepalive table takes
their ADDRESSES — never calls them; `rt_exit` parks and 41 entries are traps —
and is rooted from the boot path after the last gate marker:

```
[BOOT] SIMPLEOS-AARCH64-LIMINE-P10-ABI-PINNED symbols=85
```

`nm` on the linked kernel: **86 of 86 written symbols present, 0 GC'd**;
T-symbol count 106 -> 199; image 103 KB -> 121 KB. The *pre-existing* 11 show
the tax this avoided: 9 of them (`rt_hash_text`, the five
`rt_string_builder_*`, `rt_string_bytes`, `rt_string_len`, `rt_text_to_bytes`)
are defined in the C source but **absent from `kernel.elf`**, kept out by
having no live reference. Only `print_raw` and `stdin_read_char` survive, and
only because the P8/P9 probes call them.

**Boot gate not regressed**, verbatim last line:

```
PASS — 4 boot-stage marker(s) checked, EDK2/AAVMF pflash real-firmware aarch64
boot verified via BOOTAA64.EFI on a FAT ESP (no -kernel, no isa-debug-exit),
95 serial line(s) captured
```

One anomaly, named rather than absorbed: the line count stayed at the baseline
95 despite this change adding one serial line. The PASS does not rest on that
number — it rests on the four markers, and the new P10 marker was verified
present in the transcript by direct `grep`. EDK2 chatter varies run to run.

**The remainder, counted: 56 of the 150.** Nothing mechanical is left — every
one needs a real subsystem: filesystem `rt_file_*`/`rt_dir_*` (29), process
`rt_process_*`/`rt_shell_exec`/`rt_getpid`/`spl_thread_cpu_count` (18),
`rt_mmap`/`munmap`/`madvise`/`msync` (4), time/thread (3),
`rt_browser_renderer_*` (2, dead weight from a tool-table import). The
design decision flagged below — in-process handlers instead of CLI passthrough
— now removes 18 of those 56, and is the single largest remaining lever.

The caveat below still stands unchanged: 150 is the DECLARED-extern surface,
not the total ABI bill. Codegen-emitted calls that no `extern` declares surface
only under P6.

## STATUS UPDATE 2026-08-23 (2) — P9 IS DONE, and P10 is now INVENTORIED

P9 (guest stdout) is implemented and proven by a real boot. With P8, the byte
channel itself is off the prerequisite list.

**Another erratum in this doc, corrected.** §2 says `rt_print_str` /
`rt_println_str` / `rt_print_value` "all route to `uart_write_bytes`". They do
NOT — all four print families are `(void)value;` NO-OPS at
`freestanding_runtime.c:445-478`. The only working TX path is `log_raw_println`
(`:1537`), which is what `print_raw` was modelled on. The no-op stubs were left
alone.

**Signature, taken from the declaration rather than guessed:**
`extern fn print_raw(s: text)` — 1 arg, `text`, no return — at
`src/app/mcp/main_transport.spl:1` (NOT `main.spl`, which holds only the P8
`stdin_read_char` at `:24`). The LSP server declares it identically
(`simple_lsp_mcp/json_helpers.spl:13`); two other sites declare it returning
`i64` (`app/io/cli_ops.spl:31`, `app/dashboard/framework_policy.spl:22`). One C
symbol satisfies all four — an AAPCS64 caller that declared void just ignores x0.

**Link set confirmed exact:** `arch/aarch64/boot/` holds exactly ONE `.c`
(`freestanding_runtime.c`) plus `linker_limine.ld`, so the P10 diff below is a
complete diff, not a sample.

**Evidence.** `nm` on the linked kernel went from `0` matches for `print_raw` to
`T print_raw` / `T rt_aarch64_stdout_probe` / `T stdin_read_char`. Nonce
`0df360d912b0` appears 0 times in the old `kernel.elf` and 1 in the new one, and
the guest emitted it through the real `print_raw`:

```
[STDOUT-PROBE] via-print_raw nonce=0df360d912b0
[BOOT] SIMPLEOS-AARCH64-LIMINE-STDOUT-PROBE-DONE bytes=47
```

`bytes=47` is the exact length of that string, so the byte count round-trips.
Boot gate not regressed: `PASS — 4 boot-stage marker(s) checked ... 95 serial
line(s) captured` (93 -> 95; the delta is exactly the two probe lines). The probe
is called AFTER every marker the gate greps, so a probe failure cannot flip the
verdict.

### P10 INVENTORY — the number nobody had

Transitive `use` closure of `src/app/mcp/main.spl`: **56 modules, 0 unresolved**,
covering 20 of the 34 `src/app/mcp/*.spl` files, declaring **151 distinct
`extern fn`** symbols. Diffed against the 151 functions defined in
`freestanding_runtime.c`:

**Present (11):** `print_raw`, `stdin_read_char`, `rt_hash_text`,
`rt_string_len`, `rt_string_bytes`, `rt_text_to_bytes`,
`rt_string_builder_{new,push,finish,len,free}`.

**Missing (140):**

| bucket | n | assessment |
|---|---|---|
| `rt_simd_*` | 49 | stubbable — scalar fallbacks; dragged in by `src/lib/nogc_sync_mut/simd.spl` for one string search |
| filesystem `rt_file_*` / `rt_dir_*` | 29 | **critical path** — needs a guest FS |
| process `rt_process_*`, `rt_shell_exec`, `rt_getpid`, `spl_thread_cpu_count` | 18 | **critical path, largest unknown** — `cli_passthrough` shells out to `bin/simple` |
| text/utf8 `rt_text_*`, `rt_utf8_*`, `rt_swi_*`, `rt_rank_*`/`rt_select_*` | 19 | pure computation, straightforward ports |
| atomics / atexit / signal | 7 | stubbable |
| env/exit `rt_env_*`, `rt_exit`, `rt_platform_name`, `sys_get_args` | 5 | trivial freestanding stubs |
| `rt_mmap` / `munmap` / `madvise` / `msync` | 4 | tied to the FS work |
| stdio rest `rt_stderr_write/flush`, `rt_stdout_flush` | 3 | trivial — direct siblings of `print_raw` |
| time / thread | 3 | needs a timer source |
| `rt_browser_renderer_*` | 2 | dead weight from a tool-table import; not needed |
| `sqrt` | 1 | libm |

**Estimate:** ~90 of the 140 are stubs or pure-computation ports — mechanical.
The genuine engineering is the **47** filesystem + mmap + process symbols, and
within those the process group is the one that implies a guest PROCESS MODEL,
because MCP's CLI passthrough spawns a child `simple`. **Reducing that dependency
— in-process handlers instead of passthrough — is the cheapest way to shrink
P10**, and is a design decision worth making before anyone starts porting.

**Caveat, and it matters:** 140 is the DECLARED-extern surface. This repo has a
documented second axis — codegen-emitted runtime calls that no extern declares
(the `rt_unwrap_or_trap` NULL-GOT SEGV class,
`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`).
Those surface only when the MCP graph is actually compiled for the target, i.e.
under P6. **Do not read 140 as the total ABI bill.**

Remaining before `simple mcp` runs in-guest: P6 (full-CLI Stage 4 for
`aarch64-unknown-simpleos` — which also gates discovery of the undeclared-symbol
axis), P7 (admission receipt), P10 as inventoried, P11 (a guest boot path that
invokes the server), P12 (the gate).


## STATUS UPDATE 2026-08-23 — P8 IS DONE, and this doc had the wrong file

P8 (guest stdin) is implemented and proven by a real boot. Three errata in the
text below, corrected here rather than silently edited out:

1. **Wrong lane.** Every P8 reference below names
   `arch/arm64/boot/baremetal_stubs.c:2552`. That stub is real, but it belongs
   to the **unified/desktop** arm64 lane. The **real-firmware** lane never
   compiles it: boot-object autodiscovery keys off the ENTRY FILE's sibling
   `boot/` dir, and the real-firmware entry is `arch/aarch64/limine_entry.spl`,
   so the linked C file is `arch/aarch64/boot/freestanding_runtime.c` — which
   had no stdin symbol at all. Absent, not stubbed.
2. **Wrong symbol.** The Simple extern is the 0-arg `stdin_read_char()`, not
   `rt_stdin_read_char` (host impl: `runtime_native.c:2210`). Only the
   un-prefixed spelling satisfies the MCP/LSP externs.
3. **Wrong detector.** `check-simpleos-mcp-in-guest-qemu.shs` probed the same
   wrong path; corrected in the same change.

**Evidence a byte crossed into the guest.** Nonce `eb53846c4143`, ASCII hex
`656235333834366334313433`, fed through a pipe (not a tty, so no local echo):

```
[STDIN-PROBE] armed rounds=300
[STDIN-ECHO] len=12 hex=656235333834366334313433
[BOOT] SIMPLEOS-AARCH64-LIMINE-STDIN-PROBE-DONE bytes=12
```

The real-firmware boot gate is not regressed: `PASS — 4 boot-stage marker(s)
checked ... 93 serial line(s) captured`, rc 0 (90 baseline + 3 probe markers).

**Implementation is bounded non-blocking**: `uart_try_get_byte()` polls FR bit 4
(RXFE) up to 100000 spins, then reads `DR & 0xFF`; no data yields an empty
string, matching how the host reports EOF. It mirrors `serial_putchar`'s
existing 100000-iteration TXFF bound and the only live RX consumer
(`gui_entry_desktop.spl:364-365`, which polls `uart_data_ready()` first).
Blocking was rejected deliberately: every existing aarch64 gate runs
`-serial file:` (TX-only), so a byte can never arrive and a blocking read would
wedge the guest before it printed its boot markers. MCP's blocking-read
semantics belong in the P10 transport shim, not in the UART primitive.

**PACING IS A DESIGN INPUT, not an implementation detail.** The first attempt
sent the nonce once at t=0 and got `[STDIN-PROBE] no-data`: bytes sent before
the kernel runs are consumed by EDK2/Limine's own console. Success required a
continuous feed overlapping the guest's polling window — exactly the hazard §2.3
predicted from the riscv64 precedent. **P12's host driver must feed DURING the
window, not at VM start.**

**Do not delete the boot probe as test scaffolding.** `nm` shows
`stdin_read_char` present while `rt_stdin_read_char` and
`rt_aarch64_uart_try_get` were GC'd — `--gc-sections` keeps only what is
referenced, and `stdin_read_char` survives *only because the probe calls it*.
Strip the probe and the symbol silently vanishes again.

**P9 (`print_raw`) re-scoped down.** Verified absent from the linked kernel
(`nm | grep -c print_raw` -> 0), but the TX plumbing it needs already exists:
`rt_print_str` / `rt_println_str` / `rt_print_value` all route to
`uart_write_bytes`. P9 is a symbol shim structurally identical to P8, plus a
live reference to survive `--gc-sections`. The large unknown remains P10, the
rest of the MCP module graph's runtime ABI.


## 1. Acceptance criterion

"MCP works with simple on SimpleOS under QEMU" admits three readings. They are
not equivalent and they have wildly different prerequisite chains.

| # | Reading | What it proves | Already true? |
|---|---|---|---|
| (i) | An **MCP server process runs inside the guest**; the host is only an MCP *client* speaking JSON-RPC across the VM boundary. | SimpleOS can host a real protocol server: process, stdio, framing, dispatch. | No. |
| (ii) | An **MCP server runs on the host** and merely uses the guest as a backend (e.g. a tool that shells into QEMU). | Nothing about SimpleOS. The server never crosses the boundary. | Trivially true today (`bin/simple_mcp_server` is rc=0 on the host). |
| (iii) | **`simple` runs in-guest**, MCP exists only on the host, and the two are unrelated. | That SimpleOS can execute the Simple CLI. | No — and note this is *also* not proven: `check-simpleos-compiler-filesystem-qemu.shs:128` hardcodes `GUEST_WORKFLOW_READY=0` and every arch exits 3 `blocked`. |

**Recommendation: (i).** (ii) is excluded by construction — the honesty rule for
this work is that a gate must never measure the host instead of the guest, and
(ii) *is* measuring the host. (iii) is a strictly weaker claim that the
compiler-filesystem lane already owns and is separately blocked; adding an MCP
label to it would claim something the evidence does not support.

### 1.1 Falsifiable statement

> With a SimpleOS aarch64 guest booted under QEMU via real firmware, the host
> sends the JSON-RPC 2.0 request
> `{"jsonrpc":"2.0","id":1,"method":"initialize","params":{...}}` followed by
> `notifications/initialized` and then `{"jsonrpc":"2.0","id":2,"method":"tools/list"}`
> across the guest boundary. The guest returns, for each request, a
> syntactically valid JSON-RPC response object whose `id` matches the request's
> `id`, whose `result` is well-formed per the MCP schema, and whose
> `result.serverInfo.name` (or an equivalent agreed field) **contains the
> per-run nonce that the host injected into the guest via `-fw_cfg` and which
> appears nowhere on the host process's own command surface**.

The nonce is what makes this falsifiable rather than fabricable. A host-side
process cannot produce it without having actually read it out of the guest's
firmware-config device, which only guest code can do. The precedent is exact:
`scripts/check/lib/simpleos-compiler-filesystem-receipt.shs:82-93` already
requires a `SIMPLEOS_COMPILER_FS_FWCFG ... status=pass` line proving the guest
read `opt/simpleos.cfs.nonce`, and
`scripts/os/prepare_qemu_nonce_media.shs:66-71` shows the alternate
media-slot-patching form of the same idea.

**What makes it FAIL:** any missing response, any `id` mismatch, any malformed
JSON, any response lacking the nonce, or a response present in the log before
the host sent the corresponding request (replay).

## 2. Transport

### 2.1 The server is transport-thin — this is the keystone

`src/app/mcp/main.spl` is 491 lines and touches the outside world through
exactly two externs:

- `extern fn stdin_read_char() -> text` (`src/app/mcp/main.spl:24`, used at
  `:295` and `:306` inside `_mcp_read_line()` at `:292`)
- `print_raw` (`src/app/mcp/main_transport.spl:1`), used for both
  newline-delimited JSON and `Content-Length` framing.

So **"MCP in the guest" reduces to "give a guest process a bidirectional byte
channel bound to fd0/fd1."** No MCP-specific kernel work is implied. The
protocol layer is already written and is arch-neutral Simple.

The host-side implementation of those two symbols is libc:
`stdin_read_char` is `fgetc(stdin)` at `src/runtime/runtime_native.c:2210`;
`print_raw` is at `:2226`. Neither exists freestanding.

### 2.2 What the guest has today

**Structural note before reading the table:** SimpleOS driver *logic* lives in
`src/os/**` (`.spl`), but the freestanding runtime and the bootable entry
points live in `examples/09_embedded/simple_os/arch/<arch>/`. Searching only
`src/` yields a false "not wired" answer for every item below.

| Capability | Status | Evidence |
|---|---|---|
| PL011 UART **TX** | EXISTS | `src/os/kernel/arch/arm/pl011_common.spl:44-46` (`TXFF` spin + `UARTDR` write) |
| PL011 UART **RX** primitives | **EXISTS** | `src/os/kernel/arch/arm/pl011_common.spl:48-53` (`pl011_data_ready`, `RXFE` poll) and `:55-57` (`pl011_read_char`, reads `UARTDR & 0xFF`); wrapped as `uart_data_ready()`/`uart_read_char()` at `src/os/kernel/arch/arm64/console.spl:115,118` |
| PL011 RX **actually polled in a live boot path** | **EXISTS** | `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl:364-365` polls `uart_data_ready() == 1` then `uart_read_char()` in the desktop main loop. The RX path is live; it is simply never *fed* — the arm64 gates pin `-serial file:` (TX-only) or `-serial none`, and the four gates that do use `-serial stdio` have no harness writing to their stdin. See the sweep below. |
| `rt_stdin_read_char` wired to that RX | **NO — hard-stubbed** | `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:2552`: `RuntimeValue rt_stdin_read_char(RuntimeValue a) { (void)a; return rt_string_from_cstr(""); }` — returns empty forever, i.e. permanent EOF. Same on x86_64: `arch/x86_64/boot/rt_extras.c:1865` `NOP1(rt_stdin_read_char)` and `arch/x86_64/boot/auto_stubs.c:3895` returns `NIL_VALUE`. |
| `-fw_cfg` host→guest data injection | EXISTS (arm64 reader present) | `src/os/kernel/arch/arm64/fw_cfg_named_file.spl`; host side `src/os/_QemuRunner/scenario_exec.spl:474-488` |
| virtio-mmio ring machinery | EXISTS, complete | Simple side: `src/os/drivers/virtio/virtio_common.spl:19-63` (full MMIO register map incl. `QUEUE_DESC/AVAIL/USED`, `QUEUE_NOTIFY`), `:82-114` `Virtqueue.new()`. C side, aarch64: `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:2962-2966` (base `0x0a000000`, stride `0x200`, 32 slots) and full ring bring-up at `:3151-3230`, proven with virtio-input. |
| FAT32 read off virtio-blk | EXISTS | `baremetal_stubs.c:3864` (`rt_arm_fat32_probe_bpb_from_virtio`), `:4048` |
| FAT32 **write** | PARTIAL | No `fat32_write` symbol in `arch/arm64/boot/baremetal_stubs.c`, but a positioned backend exists: `src/os/sosix/fs/fat32_positioned_vfs_backend.spl:81` (`write_at`) over virtio-blk write. Not exercised by any gate; treat as unproven for evidence purposes. |
| virtio-console / virtio-serial | **ABSENT, and known-absent** | `scripts/check/check-simpleos-qemu-host-gpu-2d.shs:1098-1102`: "SimpleOS has no framed VirtIO-console adapter or host-daemon socket endpoint yet"; the classifier returns `virtio-serial-unimplemented` at `:1110`, mapping to `status=blocked reason=virtio-serial-guest-transport-unimplemented` at `:2716-2718`. All that exists is the device-ID constant `VIRTIO_DEVICE_CONSOLE: u32 = 3` (`src/os/drivers/virtio/virtio_common.spl:52`) and a PCI-ID→name string (`src/os/services/pcimgr/driver_match.spl:59`) — no queue setup, no read/write path. |
| virtio-vsock | ABSENT | no hits anywhere under the SimpleOS kernel or gate scripts |
| 9p / virtiofs shared FS | ABSENT | no `-fsdev`/`-virtfs`/`9p` in any `scripts/check/check-simpleos-*.shs` |

A sweep of every `scripts/check/check-simpleos-*.shs` for `-chardev`,
`-device virtio-serial*`, `virtserialport`, `virtconsole`, `vhost-vsock`,
`virtfs`, `-fsdev`, and `9p` returns **zero hits** — the only near-miss is the
shell *label* `virtio-serial-unimplemented` at
`check-simpleos-qemu-host-gpu-2d.shs:1111`. The `-serial` arguments actually
used across those scripts are: **22x `-serial file:...`** (guest→host only,
e.g. `check-simpleos-arm64-efi-real-firmware-boot.shs:136`), **4x `-serial
stdio`** (bidirectional in principle, but no harness writes to their stdin),
and **2x `-serial none`**.

So no arm64 lane has ever fed bytes *into* the guest over serial — **not
because the guest cannot receive them, but because no host harness has ever
sent them.** That distinction is the whole basis of the decision below.

Note that QEMU argv is also generated in Simple, not only in shell:
`src/os/_QemuRunner/runner_targets.spl:527-564` and
`scenario_catalog.spl:708-722`. Same story there — no chardev, no serial
device.

### 2.3 Decision: PL011 serial, `-serial stdio`, with hex-framed response markers

**Host→guest:** QEMU's stdin, via `-serial stdio`, into the guest's PL011 RX
FIFO. The RX primitives already exist (`pl011_common.spl:48-57`); the missing
piece is a freestanding `rt_stdin_read_char` that calls `pl011_read_char` and
blocks on `pl011_data_ready`, replacing the stub at `baremetal_stubs.c:2552`.

**Guest→host:** the same PL011, TX. But **not** as raw JSON. QEMU `virt`
exposes a single PL011, so kernel log lines and JSON-RPC responses would
interleave on one wire and corrupt the framing. The guest therefore emits each
response as a single marker line:

```
SIMPLEOS_MCP_RESPONSE seq=<n> nonce=<fw_cfg-nonce> response_hex=<hex>
```

Hex-encoding makes log interleaving harmless: the host extracts by marker and
decodes, so an interposed `[BOOT] ...` line cannot damage the payload. This is
not an invention — it is the established pattern in this repo:
`scripts/check/lib/simpleos-compiler-filesystem-receipt.shs:138-167` already
validates a guest `stdout_hex=` field by re-hashing it, and `:201-230` does the
same for an executed binary's output.

**Precedent that host→guest serial works at all here:**
`scripts/qemu/check_simpleos_rv64_serial_shell.shs:33-48` already drives an
in-guest shell by piping timed keystrokes into `-serial stdio`. That is riscv64,
not arm64, but it establishes the mechanism and the pacing problem (UART RX is
not buffered before the guest loop reads, so the host must pace or the guest
must poll from early boot).

### 2.4 Alternatives considered and rejected

| Alternative | Why rejected |
|---|---|
| **virtio-console / virtio-serial** | The right long-term answer — a real framed bidirectional channel, no log contamination, no pacing hazard. Rejected for milestone 1 only because the guest adapter does not exist and is explicitly recorded as unimplemented (`check-simpleos-qemu-host-gpu-2d.shs:1098-1102`). The virtio-mmio ring machinery to build it on **does** exist (virtio-blk at `baremetal_stubs.c:3739`, virtio-input at `:3033`), so this is a bounded port, not a bring-up: the aarch64 scanner and ring setup at `baremetal_stubs.c:2962-3230` already brings up device ID 18 (virtio-input); adding device ID 3 with its rx/tx queue pair is a delta on that same code. **Recommended as milestone 3.** |
| **virtio-vsock** | No guest driver, no host-side precedent in any gate, and it buys nothing over virtio-console for a single stdio stream. |
| **9p / virtiofs shared filesystem** | No guest driver; would be the largest port of any option. |
| **Shared memory (`ivshmem-plain`)** | The guest *can* map it (`check-simpleos-qemu-host-gpu-2d.shs:1098`), so this is technically live. Rejected because that comment also records it as documented for **Linux hosts**, and the development host here is darwin; and because a byte-stream protocol over a shared-memory ring needs its own framing and doorbell design that serial does not. |
| **Request-in via FAT32 file, response-out via serial** | Genuinely buildable today with *zero* new drivers (FAT32 read exists, serial TX exists; FAT32 write is only PARTIAL and unexercised — hence responses over serial, not written back to the image). Rejected as the primary because it is a **batch transcript**, not a live session: the host cannot make request *n+1* depend on response *n*, so it cannot exercise MCP's actual request/response sequencing. **Retained as the fallback** if PL011 RX wiring proves harder than expected — see §4.2. |
| **QMP `input-send-event` / `sendkey`** | Keystroke-rate, keymap-lossy, and semantically a *human input device*, not a byte stream. The existing input gate (`check-simpleos-arm64-qmp-input-evidence.shs:768-786`) sends 13 events across a whole run; a single MCP `initialize` is ~500 bytes. Categorically wrong tool. |
| **`-fw_cfg` for the requests themselves** | Read-only and fixed at VM start — it cannot carry a response back, and cannot carry request *n+1*. Retained for exactly what it is good at: injecting the one-shot **nonce**. |

## 3. Prerequisite chain

In dependency order. **EXISTS** = verified present in the tree today.
**BLOCKED** = depends on work owned elsewhere that is not done.
**NET-NEW** = must be written for this feature.

| # | Prerequisite | Status | Evidence / note |
|---|---|---|---|
| P1 | aarch64 real-firmware boot under QEMU (AAVMF → Limine `BOOTAA64.EFI` → `kernel.elf`) | **EXISTS** | `scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs:131-136`; ESP built by `scripts/os/build-simpleos-aarch64-efi-esp.shs` |
| P2 | PL011 UART TX (serial evidence out) | **EXISTS** | `src/os/kernel/arch/arm/pl011_common.spl:44-46` |
| P3 | PL011 UART RX, wired and polled in a live arm64 boot path | **EXISTS** | `src/os/kernel/arch/arm/pl011_common.spl:48-57` → `arch/arm64/console.spl:115,118` → polled at `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl:364-365`. This is the single most favourable fact in the chain: the hard part of the transport is already done and running. |
| P4 | `-fw_cfg` named-file reader on arm64 (nonce ingest) | **EXISTS** | `src/os/kernel/arch/arm64/fw_cfg_named_file.spl` |
| P5 | virtio-blk + FAT32 read on arm64 (load the payload off the image) | **EXISTS** | `baremetal_stubs.c:3739`, `:3864`, `:4048` |
| P6 | **Full-CLI Stage-4-class `simple` binary for `aarch64-unknown-simpleos`** | **BLOCKED** | Does not exist. The bootstrap CLI (`src/app/cli/bootstrap_main.spl`) exposes only `compile` and `native-build`; `mcp` lives in the full dispatch table at `src/app/cli/dispatch/table.spl:225` → `src/app/mcp/main.spl`. Owned by the bootstrap lane running separately. |
| P7 | Admitted guest payload + Stage-2 `admission.env` receipt for a **simpleos** target | **BLOCKED** | `scripts/os/provision_simpleos_guest_simple_fs.shs:104-106` rejects any builder matching `*compiler_rust*\|*simple_seed*\|*target/bootstrap*` with "pure-Simple builder provenance required"; `verify_builder_authority` (`:15-31`) demands a full Stage-2 chain. The only `admission.env` in the tree is `build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/admission.env` — a **host darwin** receipt, not a simpleos one. Downstream of P6. |
| P8 | Freestanding `rt_stdin_read_char` on arm64 wired to `pl011_read_char` | **NET-NEW** | Replaces the stub at `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:2552` |
| P9 | Freestanding `print_raw` / stdout on arm64 for the MCP writer | **NET-NEW** (likely partially present via the existing serial logger) | Host impl is `runtime_native.c:2226`; the arm64 boot stubs must route it to PL011 TX |
| P10 | Rest of the freestanding runtime ABI the MCP app's module graph pulls in | **NET-NEW, size unknown** | `doc/03_plan/os/arm64_bringup/arm64_fs_exec_freestanding_runtime_port.md` enumerates 48 unresolved symbols for the *fs-exec* graph alone; `src/app/mcp/` is 36 modules and will pull a different, probably larger set (JSON, dict, text). **This is the least-estimated item in the chain.** |
| P11 | A guest boot path that actually *invokes* the in-guest server | **BLOCKED** | The analogous compiler lane is not wired: `check-simpleos-compiler-filesystem-qemu.shs:125-134` sets `GUEST_WORKFLOW_READY=0` with the comment "Host command construction is registered, but no production guest boot path invokes `compiler_filesystem_guest_workflow_v2` yet." An MCP lane needs the same missing piece. |
| P12 | Host-side gate + MCP client driver | **NET-NEW** | §5 |
| P13 | virtio-console guest adapter (for the live, non-marker-framed transport) | **NET-NEW**, milestone 3 only | `check-simpleos-qemu-host-gpu-2d.shs:1098-1102` |

### 3.1 Admission contract: add no new role

The guest admission receipt enumerates exactly three roles —
`role_interpreter=/usr/bin/simple`, `role_compiler=/sys/apps/simple_compiler`,
`role_loader=/sys/apps/simple_loader` — asserted at
`scripts/os/provision_simpleos_guest_simple_fs.shs:85-87` and emitted at
`:221-223`.

**Decision: do not add a `role_mcp`.** Reach the server as a *subcommand of the
existing interpreter role* — `/usr/bin/simple mcp` — exactly as the host does
via `dispatch/table.spl:225`. Rationale: `validate_receipt` requires each of
the enumerated keys to appear exactly once (`:79-81`) and the emitter at
`:221-223` writes precisely three; a fourth role means editing both halves and
bumping `schema=simpleos-guest-simple-fs-v1` to a v2, invalidating every
existing receipt and every consumer of them. The subcommand route leaves the
contract byte-identical. *(Inference: I did not find a consumer that rejects
unknown extra keys, so a fourth key might validate — but the emitter would
still have to be edited, and a role the contract does not assert is not a
contract.)*

## 4. Smallest possible first milestone

### 4.1 M1 — one round trip, nonce-bound

**Not** a full MCP session. One request, one response.

1. Host generates a random nonce, launches QEMU with the P1 boot chain plus
   `-serial stdio` (replacing `-serial file:`) and
   `-fw_cfg name=opt/simpleos.mcp.nonce,string=$NONCE`.
2. Guest boots, reads the nonce via `fw_cfg_named_file.spl`, and starts
   `/usr/bin/simple mcp` reading fd0.
3. Host writes one `initialize` request to QEMU's stdin.
4. Guest's existing `_mcp_read_line()` (`src/app/mcp/main.spl:292`) consumes it
   through the newly-wired `rt_stdin_read_char`, dispatches, and emits
   `SIMPLEOS_MCP_RESPONSE seq=1 nonce=<nonce> response_hex=<hex>`.
5. Host extracts the marker, decodes the hex, and asserts: valid JSON, `id==1`,
   `result` present, nonce present, and the marker line appeared *after* the
   host's write (watermark, per the pattern at
   `check-simpleos-arm64-qmp-input-evidence.shs:706-729`).

M1 is deliberately one round trip because that is the smallest thing that
proves the whole chain end to end: guest RX, guest dispatch, guest TX, and
unforgeability. `tools/list` and `tools/call` are M2.

### 4.2 Fallback if P8 (PL011 RX wiring) stalls

Run the same assertion as a **batch transcript**: host writes the request
bytes into the FAT32 image before boot (P5's read path is already live), guest
reads them from a file instead of fd0, responses still come back as
`SIMPLEOS_MCP_RESPONSE` marker lines. This needs **zero** new drivers. It
proves guest-side MCP dispatch and nonce binding, and proves *nothing* about
live bidirectional I/O — which must then be stated in the verdict, not
silently glossed.

### 4.3 Board-runnable rule

Per `.claude/rules/board-runnable.md`, this is QEMU-developed work and must
keep a board path alive. PL011 is a **real** UART, present on every aarch64 dev
board this repo targets, and the M1 boot chain is real firmware (AAVMF pflash →
EFI application), not QEMU `-kernel` pass semantics. So the M1 design is
board-runnable *in principle*: on hardware the host side becomes a physical
serial cable instead of `-serial stdio`, and the nonce moves from `-fw_cfg` to
a provisioned file, since `fw_cfg` is a QEMU device with no board equivalent.
**That nonce substitution is a real design gap on the board path and is not
solved here.** No board run is claimed.

## 5. Gate design

A future `scripts/check/check-simpleos-mcp-in-guest-qemu.shs` should follow
Style A (single boolean claim): verdict as the last line of stdout,
`PASS — <n> ...` exit 0 / `FAIL — ...` exit 1 /
`ERROR — nothing was checked: <reason>` exit 2. A run that asserted zero things
is ERROR, never a pass.

Non-negotiable properties, each mirroring an existing gate:

- **Read rc into a variable on the line after the invocation**, never through a
  pipe (`check-simpleos-fs-toolchain-qemu-matrix.shs:106-112` is the model).
- **Self-audit the argv** for `-kernel` and `isa-debug-exit` using spliced
  string literals, per
  `check-simpleos-arm64-efi-real-firmware-boot.shs:142-149`.
- **Never measure the host.** The gate must have no code path that invokes a
  host `simple mcp`. If the guest produced no marker line, that is FAIL or
  ERROR — never a fallback measurement.
- **Nonce is mandatory.** A response without the fw_cfg nonce is FAIL, not a
  warning.
- **Fail closed on absence**: empty serial log, missing QEMU, missing firmware,
  missing payload → ERROR, never pass.
- **Atomic publication** of any receipt (`.tmp.$$` + `mv`), stale outputs
  deleted at start.

Until P6–P11 clear, the gate can only ever return ERROR. A scaffold that
returns ERROR unconditionally is honest; a scaffold with a reachable PASS path
before the guest can produce evidence is not, and must not be written.

**A scaffold has been written**: `scripts/check/check-simpleos-mcp-in-guest-qemu.shs`.
It has no PASS or FAIL emitter at all — only `oops()` — and every path ends in
exit 2. Measured 2026-08-23:

```
$ sh scripts/check/check-simpleos-mcp-in-guest-qemu.shs
ERROR — nothing was checked: P6-no-aarch64-unknown-simpleos-full-cli-payload
  (harness unimplemented; see doc/05_design/os/simpleos/mcp_in_guest_qemu_2026-08-23.md)
$ echo $?
2
```

Its `--selftest` is a set of **negative** assertions designed to catch a future
edit that makes the gate dishonest: (a) no PASS emitter exists, (b) at most two
`exit 0` sites (selftest and `--help`), (c) the file references no host MCP
server, (d) `prereq_missing` always reports something while unimplemented, and
(e) this design doc exists. It prints
`simpleos_mcp_in_guest_selftest=pass checks=5 failures=0` and exit 0 —
explicitly labelled as a selftest result, not a gate verdict. The needles in
(a) and (c) are string-spliced so those lines cannot match themselves.

The P8 probe is verified live: its pattern matches the real stub at
`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:2552` today,
so it will fire correctly once P6 and P7 clear.

## 6. What is NOT proven by this design

Even after M1 passes in full, the following remain unproven and must not be
claimed:

1. **That MCP "works" in any general sense.** M1 proves one method (`initialize`)
   round-trips. It says nothing about `tools/list`, `tools/call`, resources,
   prompts, notifications, cancellation, or concurrent requests.
2. **That the guest MCP server is the same server as the host's.** It is the
   same *source*, compiled for a different target with a different runtime ABI.
   The freestanding runtime has known divergences — see risk R2.
3. **That MCP works on any arch other than aarch64.** x86_64 and riscv64 guest
   sysroots are absent, and both have the same `rt_stdin_read_char` stub
   (`arch/x86_64/boot/rt_extras.c:1865`, `arch/x86_64/boot/auto_stubs.c:3895`).
4. **That the transport is production-shaped.** Marker-line hex framing is an
   evidence channel, not an MCP transport. A real client speaks raw stdio; this
   speaks hex-in-a-log. Closing that gap is what P13/virtio-console is for.
5. **That any of it runs on a physical board.** See §4.3 — the nonce channel
   has no board equivalent.
6. **That `simple` runs in-guest at all.** M1 depends on that; it does not
   independently establish it, and it is currently blocked (P11).
7. **Nothing about performance.** No latency, throughput, or memory figure is
   implied.
8. **If the §4.2 fallback is used, nothing about live bidirectional I/O.**

## 7. Risks

- **R1 — the acceptance criterion may be stricter than intended.** If the user
  meant reading (iii), this chain is much longer than necessary. §1 names all
  three so the choice is reversible without redoing the analysis.
- **R2 — freestanding `text` codegen landmines.** A recorded SimpleOS defect is
  that a freestanding 3-or-more-operand `text` `+` chain **silently drops
  operands**. `mcp_write_framed_message` (`src/app/mcp/main_transport.spl:4-7`)
  builds its header with exactly such a chain:
  `"Content-Length: " + str(body.len()) + "\r" + nl + "\r" + nl`. On a
  freestanding target this is a live corruption hazard that would produce a
  truncated header with no error. Use interpolation there, and expect siblings
  of this bug throughout the 36-module MCP graph.
- **R3 — P10 is unestimated.** The MCP module graph's freestanding symbol
  requirement has not been measured. It could dwarf every other item.
- **R4 — single-UART contamination.** Hex marker framing mitigates corruption
  but not *starvation*: heavy kernel logging can delay responses past a
  timeout. Mitigation: log-level gating during the MCP phase.
- **R5 — UART RX pacing.** `check_simpleos_rv64_serial_shell.shs:33-48` uses
  `sleep`-based pacing because RX is unbuffered before the guest polls. A
  ~500-byte `initialize` request may overrun a 16-byte PL011 FIFO if the guest
  is not already polling. Mitigation: chunked host writes, or a guest-emitted
  ready marker the host waits for before writing.
