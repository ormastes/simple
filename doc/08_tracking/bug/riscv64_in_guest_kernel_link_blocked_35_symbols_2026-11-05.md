# riscv64 in-guest interpreter kernel link blocked on 35 undefined rt_* symbols

- **Status:** OPEN
- **Filed:** 2026-11-05
- **Severity:** high — the in-guest Simple interpreter kernel lane cannot
  link at all; zero in-guest interpreter evidence can be produced until this
  closes.
- **Supersedes-follows:** `riscv64_in_guest_interpreter_blocked_on_baremetal_runtime_2026-08-31.md`
  (the original 43-symbol blocker, measured FIXED at tip on 2026-11-05,
  PR #6947 / lane `work/riscv-inguest-20261105`).

## Measured evidence (nonce b24836bbd2a91e8f, 2026-11-05)

Real kernel build of the interpreter row:

```
PATH=/usr/lib/llvm-18/bin:$PATH \
SIMPLE_BIN=<rust-seed> \
sh scripts/os/build-simpleos-riscv64-interpreter-kernel.shs
```

compiles 614 modules OK, then the link fails with **35 undefined symbols,
zero overlap with the original 43**. Authoritative replay per the prior
record's method: `ld.lld -T linker.ld --gc-sections --error-limit=0
--allow-multiple-definition -e <mangled spl_start> *.o` over the preserved
`.simple/native-objects-*` dir (the replay additionally reports `spl_start`,
the known vacuous artifact of the entry object living outside that dir).

Toolchain note: the default `/home/yoon/dev/llvm/install/bin/clang` has no
riscv64 target; llvm-18 on PATH does.

## The 35 symbols, by bucket

| bucket | n | symbols |
|---|---|---|
| pure computation (a sibling freestanding reference exists for each) | 8 | `rt_text_eq_any`, `rt_array_data_ptr_text`, `rt_utf8_validate`, `rt_ptr_read_i64`, `rt_atomic_int_load`, `rt_atomic_int_compare_exchange`, `rt_value_as_bool`, `rt_value_truthy` |
| no VFS/process/threads in S-mode (honest resolution = fail closed) | 14 | `rt_io_file_{open,open_read,open_write,open_append,read,seek,close_value}`, `rt_process_run{,_bounded,_tuple,_bounded_tuple}`, `rt_thread_sleep`, `rt_signal_check`, `rt_atexit_check` |
| identity/capability queries | 3 | `rt_is_interpreter_runtime`, `rt_is_jit_runtime`, `spl_thread_cpu_count` |
| adaptive-collection capture-note instrumentation | 6 | `spl_collection_capture_note_{size,lookup,materialization,hash_probe,filter,loop}` |
| session/transient heap (no freestanding sibling anywhere in the tree) | 4 | `rt_session_alloc_{begin,end}`, `rt_transient_heap_adopt`, `rt_transient_array_scope_state_v1` |

Referencing checked-in sources: `bootstrap_mir_store.spl` /
`bootstrap_hir_store.spl` (session heap, from `f1e2edad6c7`
"session-owned bootstrap MIR registries"), `interpreter_run_abi.spl`,
`text_extern_abi.spl`, parser modules (`rt_value_truthy`), and
`src/lib/nogc_sync_mut/sffi/collection_capture.spl`.

Note on `rt_text_eq_any`: PR #6957 ported it to the *embedded simple_os*
runtime (`examples/09_embedded/simple_os/arch/common/riscv_common.h`); this
kernel lane links the `src/os/kernel/arch/riscv64` runtime, a different
translation unit set, so the symbol is still undefined here.

## Required resolution

1. Port the pure-computation bucket to the kernel freestanding runtime
   (`src/os/kernel/arch/riscv64/boot/`), mirroring an existing sibling
   freestanding lane's semantics (see PR #6957's nil-aware,
   content-comparing `rt_text_eq_any` as the quality bar).
2. Session/transient heap: design first. No freestanding sibling exists;
   a drive-by port risks the silent-lie class (heap state silently wrong
   in-guest). The port needs an in-guest OpenSBI boot to verify.
3. io/process/thread and capability-query buckets: if the kernel truly
   cannot provide them in S-mode, the referencing compiler modules must
   fail closed at kernel-build time (explicit `@cfg`-style exclusion or an
   admitted-stub that traps with a named message), not leave the link
   undefined.
4. Capture-note instrumentation: provide no-op-with-note definitions or
   exclude the referencing module from the kernel closure.

## Acceptance

`sh scripts/os/build-simpleos-riscv64-interpreter-kernel.shs` links
successfully, and the resulting kernel boots under OpenSBI in QEMU far
enough to print its first interpreter marker (the lane's existing
run-riscv64 probe harness may be reused).

---

## 2026-11-05 — RESOLUTION (lane `work/riscv35-kernel-port-20261105`)

**Status: LINK BLOCKER CLOSED.** Both kernels build and link with zero
undefined symbols, and the interpreter kernel boots under real OpenSBI
v1.4 `fw_payload` to its interpreter markers. Per-bucket outcomes and
the exact commands below.

### A pre-link blocker found and fixed first (same tip)

The record's "compiles 614 modules OK" was NOT reproducible at
`origin/release/1.0.0` (`bc3e9b48cb4`): the closure compile failed
deterministically (8/8 attempts, two seeds: the checked-in bootstrap
seed rebuilt 18:12 today from the main tree, and a fresh seed built
from this branch's own `src/compiler_rust`) with

```
src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:
hir: Cannot infer field type: struct 'ANY' field 'kind'
```

Root-caused with a temporary instrumented seed (since reverted; the
instrumentation is not part of this change): the `#6675`-form code
added 2026-11-05 15:41 (`af256235c17`, PR #6924/#6961 family) reads
`present_target.kind` where `present_target` is the `if val` payload of
`_sffi_tuple_get<HirType>(...)`. In this flatten context the seed lowerer
types that payload `ANY`, and the receiver-blind `.kind` lookup then
fails closed on ambiguity (many flattened structs carry a `kind`
field). Fixed in-source, semantics-preserving, at
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`: the kind read
routes through a new typed helper `_hir_type_kind_of_bare(value: HirType)
-> HirTypeKind` (same value, same copy discipline as the bare rebuild;
the helper's parameter type keeps the receiver layout known where a
bare access on the `ANY` payload cannot). This is the same workaround
family the tree already documents at
`src/compiler/50.mir/hir_declaration_types_v1.spl:11-16`.

### Bucket outcomes (interpreter row, 33 symbols measured on the real link)

The measured link-time set at this tip is 33 symbols — the record's 35
minus `rt_text_eq_any`, which this lane's runtime already defines via
`examples/09_embedded/simple_os/arch/common/riscv_common.h` (included by
`baremetal_stubs.c`), as PR #6957's note anticipated might differ.

All ports landed in
`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c`
(the TU the previous tranches used; whitelisted for both normal and
`SIMPLE_BOOT_MINIMAL` boot autodiscovery). Signatures follow the ABI
authority the file already names — `runtime_sffi.rs`'s RuntimeFuncSpec
table — not the sibling .c files where they disagree.

| bucket | n | outcome |
|---|---|---|
| pure computation | 7 | **ported, real semantics**: `rt_array_data_ptr_text`, `rt_utf8_validate`, `rt_ptr_read_i64`, `rt_atomic_int_load`, `rt_atomic_int_compare_exchange`, `rt_value_as_bool`, `rt_value_truthy`. `rt_value_as_bool` mirrors the hosted twin (tagged-true equality, runtime_native.c:4238), NOT the x86_64 sibling's truthiness body, which contradicts the hosted contract. `rt_utf8_validate` refuses (0) a non-array input like the hosted twin; the aarch64 sibling's valid-for-nil answer is recorded as a divergence, not copied. `rt_value_truthy` mirrors hosted `rt_core_value_truthy`, including the fail-closed char trap. |
| io/process/thread | 17 | **named fail-closed traps** via a shared `rv_runtime_trap_unimplemented` (prints the symbol over the same serial sink as `rt_unwrap_or_trap`, parks in WFI) — the aarch64 freestanding sibling's `SPL_P10_TRAP` pattern. The x86_64 sibling's silent NIL no-ops for the same names are the silent-lie class and were not copied. Exception, mirroring the aarch64 sibling with its documented caller contract: `rt_signal_check`/`rt_atexit_check` return 0 ("nothing pending" — true: no signal/atexit subsystem in-guest; `signal_stubs.spl` reads `<= 0` as not-installed). |
| capability queries | 3 | `rt_is_interpreter_runtime`/`rt_is_jit_runtime`/`spl_thread_cpu_count`: **named traps**. No honest static answer exists (the guest's hart count is a boot property; the runtime-kind answers route real behavior in `flat_pool_packed_v1.spl:1051`), and the record's bucket rule is fail closed. The x86_64 sibling's hardcoded `spl_thread_cpu_count = 1` is uniprocessor drift and was not copied. |
| capture-note | 6 | **no-op-with-note**: all six `spl_collection_capture_note_*` return 1 — the hosted "no capture session active" answer (runtime_collection_capture_impl.h returns 1 inactive on every path). A freestanding in-guest kernel can never begin a capture session, so "inactive" is the true state, not a fudge. Referencing module not excluded (no exclusion mechanism exists; the gate's whole design is closure-based). |
| session/transient heap | 4 | **partially addressed, as the task permitted**: `rt_session_alloc_begin/end` return 0 and `rt_transient_array_scope_state_v1` returns 0 — the hosted "no live session / no scope running" answers (runtime_native.c:3539-3549), which keep the bootstrap stores' `session_on = false` and select the pre-session LEGACY append+promote path that this guest row booted with before the session discipline existed. `rt_transient_heap_adopt` is a **named trap**: adopt is reachable only from the session publish path, and there no return value is truthful. No freestanding sibling for this discipline exists anywhere in the tree (checked aarch64/x86_64 freestanding runtimes and `src/os/kernel/arch/*`), and this change does not invent one — a real in-guest session heap still needs the design session this record calls for. |

Exclusion vs stub, per symbol: no closure-exclusion mechanism exists
for a referencing compiler module (the build is `--entry-closure`;
nothing like `@cfg` excludes a module), so every symbol above is
resolved by a port or an admitted stub — none by exclusion.

### Build-and-run row: a further 9-symbol gap (same build script)

`build-simpleos-riscv64-interpreter-kernel.shs` builds BOTH rows; the
buildrun row's closure references 9 names the interpreter row does not.
Same file, same rules: `rt_tuple_len`, `rt_value_nil`, `rt_value_is_nil`,
`rt_value_is_int`, `rt_array_sorted` (full hosted-comparator port: new
array, text/int/float ordering, mixed types Equal), and
`rt_heap_ref_registered` (mirrors the hosted SIMPLE_CORE_C_STANDALONE
wellformed twin — the strict registry probe would refuse every
bump-arena HIR node, the documented Phase-3 failure) are real ports;
`rt_mem_snapshot_open` returns -1 (hosted fail-closed setup failure; the
caller disables recording), `rt_mem_snapshot_record` and
`rt_file_read_regular_no_follow_bounded_bytes` are named traps, and
`rt_file_read_regular_no_follow_last_failure` returns the hosted
"never called" sentinel 77.

### Boot blocker found and fixed: the duplicate-allocator lottery

With the link closed, the interpreter kernel booted but parked before
any `[interp]` banner:

```
[TRAP] S-mode exception, the guest is parking here
[TRAP]   scause=0x0000000000000007 sepc=0x0000000080333e48 stval=0
```

`sepc` is inside `parser_state_fresh` (a module-init global): the
ParserState allocation returned NULL and the unchecked struct store
faulted. Root cause: THREE boot TUs define global
`malloc`/`calloc`/`rt_alloc` (baremetal_stubs.c, baremetal_runtime_core.inc.c,
ghdl_boot_info_runtime.c); the link resolves them with
`--allow-multiple-definition`, so exactly ONE copy serves the whole
image and the choice is a link-order lottery. The 2026-11-05 closure's
lottery landed on `ghdl_boot_info_runtime.c`, whose heap is a private
**64 KiB** static array — exhausted within the first megabyte-scale of
module-init allocations. Fixed in that TU: the array is 32 MiB (.bss is
NOLOAD, so the flat Image does not grow; 512M RAM backs it), with a
comment stating the invariant that every duplicate must be able to
serve the whole image. (The heap-exhaustion report never printed
because the winning copy's `rv_alloc` has no report hook — the silent
NULL is exactly the failure mode `baremetal_bump_heap.h`'s header
documents.)

### Evidence

Build (both rows, zero undefined symbols):

```
PATH=/usr/lib/llvm-18/bin:$PATH \
SIMPLE_BIN=<seed built from this branch's src/compiler_rust> \
sh scripts/os/build-simpleos-riscv64-interpreter-kernel.shs
# -> PASS — riscv64 interpreter + build-and-run kernels built by the RUST SEED
#    interp:    kernel.elf 5268032 bytes + kernel.Image 4602080 bytes
#    buildrun:  kernel.elf 14934640 bytes + kernel.Image 13883840 bytes
```

Toolchain note unchanged: the default `/home/yoon/dev/llvm/install/bin/clang`
has no riscv64 target; llvm-18 on PATH does. Seed note: the checked-in
bootstrap seed (rebuilt 18:12 today from the main tree, whose
compiler_rust diverges from this branch) reproduces the compile blocker
above identically; the evidence above uses a seed built from THIS
branch's `src/compiler_rust` (`cargo build --release --bin simple`), per
the build script's own header requirement.

Boot (interpreter row, real OpenSBI v1.4 `fw_payload`, pinned
`a2b255b88918...`, argv self-checked, `-bios` only, embed assertion
passed — the row's own kernel.Image verified verbatim inside
fw_payload.bin):

```
qemu-system-riscv64 -no-user-config -machine virt -cpu rv64 -smp 1 -m 512M \
  -bios interp-fw_payload.bin -serial file:interp-serial.log \
  -display none -monitor none -net none -no-reboot   # timeout 180
```

Serial transcript ( preserved at `/tmp/rv-boot/interp-serial2.log` on the
measurement host; reproduced here from the tail), OpenSBI v1.4 banner
omitted:

```
[interp] SimpleOS riscv64 in-guest Simple interpreter (OpenSBI fw_payload)
[interp] serial up, interpreting a hello world
[interp] lowering hello-world source through the real frontend
[TRAP] rv64 freestanding kernel runtime: `rt_process_run` was called. No host
[TRAP] subsystem backs this entry point in the in-guest S-mode kernel.
[TRAP] Named trap stub, not an implementation. Core parked.
```

The gate's `interp_boot_ok` precondition set (OpenSBI banner + both
`[interp]` rungs) is satisfied, and the row proceeds INTO the real
frontend -- further in-guest than any prior measurement on this lane.
The first host dependency the frontend reaches is arch detection for
`@cfg` evaluation: `_pp_preprocess_conditionals` evaluates cfg keys via
`cfg_platform.spl`, whose `host_arch()` shells out to `uname -m`
(`src/compiler/10.frontend/core/cfg_platform.spl:205`); the named trap
is exactly the record's prescribed fail-closed behaviour, and it names
the call site class precisely. Returning a fabricated `uname` result
would silently evaluate `@cfg` guards wrong -- the silent-lie class this
record exists to prevent -- so the trap stands. The row-level nonce
print therefore remains gated on a future freestanding arch-detection
owner (or a frontend path that does not consult the host), which is the
next row-level defect after this record.

The buildrun row boots identically under the same harness (same OpenSBI
pin, same argv policy, embed assertion passed): serial shows the
`[buildrun]` banner, both `[buildrun]` rungs, and "lowering source
through the real frontend", then the same named `rt_process_run` trap.
Both rows' `kernel.elf` pass the gate's weak-nil-stub `nm` check with
zero undefined and zero weak `rt_*` symbols.

### Not addressed here

- The session/transient-heap DESIGN (bucket 4 is deliberately partial;
  see above).
- The next row-level blocker the boot now reaches: freestanding
  `@cfg` arch detection (`cfg_platform.spl` `host_arch()` shells out to
  `uname -m`; see the boot evidence above). The pre-existing Defect A
  parser StringLit issue from the superseded record was NOT reached by
  this boot -- the frontend stops earlier, at preprocessing -- so its
  status at this closure is unmeasured.
- The `.simple/native-objects-*` ld.lld replay continues to report
  `spl_start` undefined (the known vacuous artifact documented in the
  superseded record); the real build script remains the only honest
  measurement.
