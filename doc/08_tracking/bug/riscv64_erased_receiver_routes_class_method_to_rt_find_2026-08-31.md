# riscv64 mcp row: an erased (`ANY`) receiver routes a user `me` method to `rt_find`, which reads a type header class instances do not have

Status: OPEN — root-caused end to end, no fix shipped.
Arch: riscv64 freestanding (SimpleOS, OpenSBI `-bios fw_payload`)
Gate: `scripts/check/check-simpleos-riscv64-components-in-guest-opensbi.shs`
Filed: 2026-08-31

## Supersedes two earlier framings

* `simpleos_riscv64_component_rows_lose_string_content_2026-08-31.md` — the
  "three rows lose string CONTENT" premise is **STALE**. Measured at
  `origin/main` (`ea48917812b`, tip = PR #198) with a freshly built Rust seed:
  **caret, devtool and testrun are all GREEN in-guest**, including
  `[caret] extracted content=CARET_RTT_CONTENT` and
  `[testrun] parser reported passed=2`. Only `mcp` fails.
* `freestanding_riscv64_for_in_array_yields_nil_after_first_element_2026-08-31.md`
  — also **STALE**. The whole text-primitive probe, including the steps that
  record lists as WRONG (9d, 9e, 9h, 9k), is GREEN at `origin/main`. The
  `for`-loop element fetch is correct. Verbatim: `9e` traces all seven
  characters (`" u s e r " }`) and `9k` prints `ch.len = EXPECTED` seven times.

Neither the module-level-global lead nor the `BoxInt` tagging lead is
implicated. The `BoxInt` hypothesis is additionally **disproved by
construction**: the freestanding `rt_index_arg`
(`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c:278`) returns
`value >> 3` for a tagged int and the value **unchanged** otherwise, so it
tolerates a raw index; a dropped tag could not produce the reported symptom.

## Current state

```
FAIL — 4 component(s) checked in-guest on SimpleOS riscv64 under real OpenSBI
firmware via -bios fw_payload, 1 failed: mcp
```

3 of 4 riscv64 rows green.

## The defect

The mcp row stops after `probe m3e`. The next statement is

```
val probe_find = reg.find("no_such_tool_at_all")
```

and it traps, re-entering the kernel (the boot sequence repeats 2,315 times in
one 409,392-line serial log, with a single OpenSBI banner — a trap, not a
machine reset).

### Chain, each link measured

1. **The receiver is type-erased.** `SIMPLE_DUMP_MIR=1` on the real entry gives

   ```
   Load             { dest: VReg(75), addr: VReg(76), ty: TypeId(14) }
   MethodCallStatic { dest: Some(VReg(78)), receiver: VReg(75), func_name: "find", args: [VReg(77)] }
   MethodCallStatic { dest: Some(VReg(95)), receiver: VReg(91), func_name: "register", args: [VReg(93)] }
   ```

   `TypeId(14)` is `TypeId::ANY` (`hir/types/type_system.rs:112`). Both method
   names are **bare** — the class type of `var reg = DispatchRegistry.new_for_test()`
   is lost, so neither call is qualified as `DispatchRegistry.<m>`.

2. **A bare name in the erased-collection set is routed to the builtin before
   any user-method resolution.** `codegen/instr/closures_structs.rs:737-750`:

   ```rust
   let bare_builtin_collection =
       !lookup_name.contains('.') && is_bare_builtin_collection_method(lookup_name, args.len());
   ```

   `is_bare_builtin_collection_method` (same file, :113) lists `("find", 1)`
   at :119. `register` is **not** in that set, which is exactly why
   `reg.register(entry)` resolves correctly to
   `DispatchRegistry_dot_register` while `reg.find(...)` does not. This
   ordering is deliberate (bug #62, 2026-07-02) and correct for genuinely
   erased Dict/Set receivers; it has no way to tell those from a class.

3. **Confirmed in the linked artifact.** In `dispatch_wrap`, where `reg` is a
   TYPED parameter, the call site resolves to
   `DispatchRegistry_dot_find`. In the entry's `mcp_component_row`, the
   identical source-level call resolves to **`rt_find`**.

4. **`rt_find` reads a type header that class instances do not have.**
   Disassembled from the linked `kernel.elf`:

   ```
   rt_find:
     andi a0,a0,7 ; li a1,1 ; beq  -> tag must be 1 (heap), else return -1
     andi a0,a0,-8                  -> untag to base pointer
     lw   a0,0(a0)                  -> read a 32-bit TYPE header at offset 0
     li   a1,1 ; bne -> dispatch on it
   ```

   But a class instance carries no header. `DispatchRegistry.new_for_test`
   allocates `rt_alloc(24)` and stores its three fields at offsets **0, 8, 16**,
   then tags with `ori a0,a0,1` — the same heap tag `RtString`/`RtArray` use.
   So `lw a0,0(a0)` reads the low 32 bits of the `entries` array HANDLE as if it
   were a type tag, and dispatch proceeds on garbage.

**Root cause, one sentence:** class instances are tagged as heap objects but
carry no type header, so any tag-dispatching runtime helper that a type-erased
receiver routes them into misreads them — and the erased-receiver heuristic
routes a user `me` method named `find` into exactly such a helper.

## Why the sibling arches are green

This lowering is arch-independent, so x86_64 and aarch64 emit the call to
`rt_find` too. They survive because their `rt_find` reaches a path that answers
the `-1` miss sentinel instead of dereferencing. The row's `probe m3f` only
prints which branch it took and gates no rung, so a wrong `-1` is invisible
there. **The mis-resolution is therefore latent on every arch**; only riscv64
turns it into a trap.

## Defect class

`find` is not the only exposed name. Every entry in
`is_bare_builtin_collection_method` shadows a same-named user `me` method on an
erased receiver: `get`, `has`/`contains`/`contains_key`/`has_key`, `remove`,
`find`, `starts_with`/`ends_with`, `slice`. Any class in this tree defining one
of those is on the same footing.

## Method notes for the next reader (two traps cost real time here)

* **`objdump` symbol grep undercounts calls to near-zero on this lane.** Simple's
  freestanding codegen emits calls indirectly through an inline literal pool:
  `auipc rX,0x0 ; ld rX,12(rX) ; j +12 ; <8 bytes of absolute address> ; jalr rX`.
  The 8-byte target disassembles as garbage instructions, so
  `objdump -d | grep rt_index_get` reports **zero call sites** in a binary that
  calls it seven times. Resolve targets by reading the literal pool. Any
  grep-based claim in the older riscv64 records (e.g. "`rt_pool_safepoint`'s
  linked body is a no-op", "`core.inc.c` reaches no binary") should be
  re-verified this way before it is relied on.
* **The winning TU for this lane is
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`** — not
  `baremetal_stubs.c` and not `baremetal_runtime_core.inc.c`. It defines
  `rt_index_get`, `rt_array_get`, `rt_for_iterable`, `rt_value_int`,
  `rt_index_arg`. It does **not** define `rt_find`, whose provenance was not
  identified.

## Fix directions, in preference order

1. **HIR**: infer the class type for `var x = Class.static_ctor()` so the call
   lowers qualified as `DispatchRegistry.find` and never reaches the erased
   heuristic. Cross-module inference already works for a smaller fixture
   (`build/mrepro/g.spl` lowers `Reg.find` qualified), so this is a narrowing
   of an existing capability, not new machinery.
2. **Object model**: give class instances the same type header the
   tag-dispatched helpers already assume. Correct but architectural — needs the
   user's approval before anyone starts.
3. **NOT acceptable**: renaming the product method `find`. That normalizes a
   workaround and leaves the whole defect class live.
