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
  `rt_index_arg`. It does **not** define `rt_find` — that comes from
  `src/runtime/runtime_native.c:8328`, the HOSTED runtime — and it does **not**
  define `rt_string_bytes` either. How a freestanding link ends up served by the
  hosted runtime for these two entry points is unresolved, and is the leading
  question for the residual `.bytes()` defect recorded below.

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


## Confirmed in-guest by a controlled experiment (2026-08-31)

Changing ONLY the receiver's typing in the entry —

```
-    var reg = DispatchRegistry.new_for_test()
+    var reg: DispatchRegistry = DispatchRegistry.new_for_test()
```

— makes MIR store the local as `TypeId(88)` instead of `TypeId(14)`/ANY and
lowers **both** calls qualified (`DispatchRegistry.find`,
`DispatchRegistry.register`). In-guest the trap disappears completely: the
serial log drops from **409,392 lines to 102**, and the row advances through
every previously-unreachable step:

```
[mcp] probe m3f me-method self-field READ ok (miss, as expected)
[mcp] probe m4 register ok
[mcp] probe m5 AuthorityToken.root_for ok
[mcp] request  tool=echo args=[MCP_RTT_PAYLOAD]
[mcp] response {"status":"ok","body":"MC
[mcp] request  tool=no_such_tool_xyz (must be refused)
[mcp] response {"status":"error","code":"unregistered_tool","reason":"no handler for: no_such_tool_xyz"}
[mcp] FAIL registered dispatch lost the payload
```

This is the causal proof: the ANY-erasure is the whole cause of the **trap**.

**The annotation is a DIAGNOSTIC ONLY and was reverted.** It is not committed
and must not be adopted as an idiom — it hides a compiler defect at one call
site and leaves the whole class live.

## The trap is not the last rung — a SECOND, independent defect remains

With the receiver typed, mcp still FAILs, and the reason is now precisely
visible and is the original "string content" symptom, narrowed to one path:

```
[mcp] response {"status":"ok","body":"MC
```

The echoed body is `MC` — the first two bytes of `MCP_RTT_PAYLOAD` — and the
envelope's own trailing `"}` never prints, with no `\r` terminating the line.
The whole `_ok_envelope` string stops mid-way, which is the signature of an
embedded NUL reached by `serial_println`, not of a short body. The suspect path
is `_echo_handler`'s `s.bytes()` -> `_gate_filtered` -> `_bytes_text`
(`src/lib/nogc_async_mut/mcp/dispatch.spl:161-167`), whose loop is
`while i < b.len(): result = result + char_from_code(b[i] as i64)`. Note that
`rt_string_bytes` is **not defined in the winning freestanding TU**, so `.bytes()`
is served by a translation unit that may not share this runtime's array/string
layout — the same provenance question as `rt_find`.

`devtool`, `caret` and `testrun` never take that path, which is why they are green.

## Corrected fix targets

Fix direction 1 in the list above named
`hir/lower/expr/simd.rs::lower_static_method_call` as the site that erases the
local to ANY. That is **not established**, and the first attempt to disprove it
was itself invalid — see the instrumentation warning below. The MIR emits
`Call Pure("lib__nogc_async_mut__mcp__dispatch__DispatchRegistry_dot_new_for_test")`,
a fully module-qualified symbol, not the `"{class}.{method}"` shape that
function builds, so an IMPORTED static method takes a different lowering path.
A candidate fix that consulted `resolve_type`'s `global_struct_defs` fallback
there was written, compiled, and **reverted after measuring it had no effect**.
Valid file-based instrumentation later explained why it could not help: for every
class `lower_static_method_call` actually sees, `module.types.lookup` and
`globals` ALREADY succeed (135 probe rows, e.g.
`qualified=BinaryReader.new resolve_type=Some(TypeId(87)) types.lookup=Some(TypeId(87))
globals=Some(TypeId(87))`), so an extra `resolve_type` fallback is unreachable.

**Where the erasure is NOT.** Two lowering paths were instrumented and cleared:
`hir/lower/expr/mod.rs::call_return_type` runs 8,372 times in this compile and
**not once** with a callee whose `Debug` mentions `DispatchRegistry` or
`new_for_test`; `lower_static_method_call` runs 135 times, all for stdlib
classes, and never for `DispatchRegistry`/`DispatchEntry`/`AuthorityToken`. So
the ENTRY module's own statements are lowered by a pass neither probe covers.
Locating that pass is the first task for whoever picks this up.

### Instrumentation warning — this cost two wrong conclusions

**Environment variables do NOT reach the process that performs HIR lowering for
this lane, and its stderr is not forwarded either.** An `eprintln!` guarded by
`std::env::var("SIMPLE_DEBUG_...").is_ok()` produces **zero output even from code
that provably runs thousands of times**. `SIMPLE_DUMP_MIR` works only because it
is read later, in `codegen/common_backend.rs:2155`, in a process that does see
the variable. An earlier revision of this record concluded from such a silent
probe that `lower_static_method_call` is "never entered"; an UNGUARDED probe
writing to a FILE proved it is entered 135 times. Instrument this pipeline by
appending to an absolute path with no env guard, and never read silence as
evidence.

So closing all four rows needs **both**:

1. Type the local from an IMPORTED static method's declared return type, in
   whichever lowering path actually handles it, so the call lowers qualified.
2. Fix the `.bytes()` / `_bytes_text` round-trip on this lane (or resolve the
   TU-provenance question that makes `rt_string_bytes` and `rt_find` come from
   the hosted runtime).

---

## 2026-08-31 — partial fix landed; the erasure is confined to the `--entry-closure` lane

### What was fixed

The defect class named above is real and is now fixed **on the ordinary lowering
path**, with a value-asserting JIT test that needs no QEMU:
`src/compiler_rust/compiler/tests/erased_receiver_user_method_shadowed_by_builtin_jit.rs`.

Verified RED before / GREEN after, verbatim:

```
# before
test erased_class_receiver_runs_its_own_find_not_the_builtin ... FAILED
  left: -1
 right: 42
test result: FAILED. 2 passed; 1 failed

# after
test result: ok. 3 passed; 0 failed
```

`left: -1` is the builtin's miss sentinel, which **confirms the record's claim
that the mis-resolution is latent on x86_64/aarch64 too** — it is not a
riscv64-only defect, it is merely not fatal elsewhere.

Fix: `mir/lower/lowering_core.rs` (`compute_single_assignment_class_types` +
`collect_local_writes`, and the `erased_local_class_types` field recomputed per
function) and `mir/lower/lowering_expr_method.rs` (a new rung in the `func_name`
chain). When a receiver is erased AND the method name is in
`is_bare_builtin_collection_method`, the class is recovered from the local's
SINGLE reaching definition and the call is emitted qualified, so it never
reaches the heuristic.

Deliberately conservative, so bug #62 is preserved untouched: single-assignment
locals only, never a parameter, never a local that already resolves to a name,
and only `HirType::Struct`. Arrays and dicts are excluded **because they share
the same TypeId range as classes** — measured on this tree: array `TypeId(18)`,
dict `TypeId(19)`, class `TypeId(16)`. A third test asserts a genuine erased
text receiver still reaches the builtin.

### Why this did NOT close the mcp row

The riscv64 gate is still red, verdict unchanged in kind:

```
FAIL — 4 component(s) checked in-guest on SimpleOS riscv64 under real OpenSBI
firmware via -bios fw_payload, 1 failed: mcp; serial log: ... (391399 lines)
```

(Baseline before the change on the same tree: 406,243 lines. Both are the trap
loop; the difference is not meaningful.)

### New boundary evidence — where the erasure actually lives

This narrows the record's open "locate that pass" item from the other side.
**Every hosted fixture already lowers `find` QUALIFIED, including the real
import.** Measured with `SIMPLE_DUMP_MIR=1`:

| fixture | `new_for_test` call target | `find` lowers as |
|---|---|---|
| same-module `struct` + `static fn` | `Pure("Registry.new_for_test")` | `Registry.find` |
| cross-module sibling file | `Pure("Registry.new_for_test")` | `Registry.find` |
| cross-module `class` + implicit return | `Pure("Registry.new_for_test")` | `Registry.find` |
| **real** `use lib.nogc_async_mut.mcp.dispatch.{DispatchRegistry}` | `Pure("DispatchRegistry.new_for_test")` | `DispatchRegistry.find` |

In all four the new fix fired **zero** times (`SIMPLE_DEBUG_METHOD_DISPATCH=1`),
because nothing was erased in the first place. So the shape of the source is NOT
what causes the erasure — not `class` vs `struct`, not the implicit return, not
cross-module, and not the stdlib import path.

The erasure is specific to the **`native-build --entry-closure`** lane the gate
uses. Running that exact invocation on the real entry:

```
simple native-build --backend cranelift --entry-closure --timeout 1200 \
  --entry examples/09_embedded/simple_os/arch/riscv64/toolchain_components_entry.spl \
  --target riscv64gc-unknown-none-elf ...
```

still yields **10 bare `func_name: "find"`** call sites, the receiver `Load`
still carries `ty: TypeId(14)` (ANY), and the new rung fires **0** times. That
is the ground truth: `--entry-closure` flattening produces HIR for the entry's
own statements in which the initializer expression itself is untyped, so
single-assignment provenance has nothing to recover.

**Next reader: the remaining work is in the `--entry-closure` flattening path,
not in method lowering.** Note this lane is also where the record's mangled
`lib__nogc_async_mut__mcp__dispatch__DispatchRegistry_dot_new_for_test` symbol
comes from — the hosted lane emits the short `DispatchRegistry.new_for_test`
instead. That symbol-shape difference is the cheapest signal for telling the two
paths apart.

Both documented instrumentation traps were respected: no grep-based absence
claim about call sites, and no env-guarded `eprintln!` was read as evidence —
every conclusion above rests on a MIR dump or an asserted value.

### Still open

1. The `--entry-closure` erasure above (blocks the mcp trap).
2. The separate `.bytes()` / `_bytes_text` truncation (`"MC`), untouched here.
