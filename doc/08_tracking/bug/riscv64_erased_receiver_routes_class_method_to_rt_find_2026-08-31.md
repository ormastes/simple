# riscv64 mcp row: an erased (`ANY`) receiver routes a user `me` method to `rt_find`, which reads a type header class instances do not have

Status: ALL THREE DEFECTS FIXED (2026-09-01) — the mcp row is GREEN and the
riscv64 component gate is **4 of 4**. Defect 1 (ANY-erasure trap) closed by a
compiler fix; defect 2 (`.bytes()` payload truncation) closed by tagging the
byte slots in `baremetal_runtime_core.inc.c`; a third defect found in front of
it (the #209-exposed link failure, pre-existing at `origin/main`) closed by
porting three constructors. See the three dated sections at the end of this
record. NOTE: this record's "winning TU is freestanding_runtime.c" claim is
WRONG and is corrected in the defect-2 section.
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


## Defect 1 FIXED — 2026-09-01, measured in-guest at `origin/main` c0cae452481

Two commits, both on top of `c0cae452481` (tip = PR #205), seed rebuilt between
each. Fix direction 1 from the list above, as written — no object-model change,
no product method renamed, no annotation adopted.

### What was actually wrong: TWO missing rungs, not one

The record above named `lower_static_method_call` as the erasure site and marked
it "not established". It is not the site. The real chain has two independent
gaps, and closing either alone leaves the trap intact — measured, not reasoned:

1. **No `fn_return_types` row existed for the callee.** #202 added the qualified
   `"{Type}.{method}"` return-type capture to `imports.rs`'s `Node::Impl` arm
   ONLY. `Node::Class`, `Node::Struct` and `Node::Extend` declare their methods
   INLINE and were left without it. `DispatchRegistry` is a `class` with an
   inline `static fn new_for_test()`, so it had no row at all — which is exactly
   why #202's rung "fired zero times" here. Fixed by extracting
   `record_method_return_type()` and wiring all four arms through it.

   **This alone changed nothing in-guest.** Rerun with only this fix: still
   `FAIL ... 1 failed: mcp`, serial log still 238,124 lines, row still stopping
   at `probe m3e`, MIR still emitting a bare `MethodCallStatic{"find"}` on
   `VReg(75)` with `Load ... ty: TypeId(14)`.

2. **The recovered type name was never applied to the binding's TypeId.**
   `stmt_lowering.rs:413` looked the name up and stored it in
   `ctx.static_call_type_hints` — a map with exactly ONE consumer,
   `expr/access.rs:729`, which handles ambiguous FIELD access. Method-call
   lowering never reads it. So the local stayed `TypeId::ANY` and MIR still
   emitted the bare name. Fixed by upgrading `ty` to
   `self.module.types.lookup(&hint)` when that resolves, keeping the name-hint
   insert as the fallback for types this module has not registered.

### Evidence

MIR at the gate's real `native-build --entry-closure` invocation, after both
fixes — both calls qualified, matching the annotation experiment exactly:

```
func_name: "DispatchRegistry.find"      (2)
func_name: "DispatchRegistry.register"  (1)
```

In-guest, same gate, same firmware (`-bios fw_payload`, no `-kernel`, no
`isa-debug-exit`), seed rebuilt from the patched tree:

| | baseline `c0cae452481` | + fix 1 only | + fix 1 and 2 |
|---|---|---|---|
| serial log | 331,773 lines | 238,124 lines | **102 lines** |
| furthest probe | `m3e` | `m3e` | `m5`, then the real round-trip |
| verdict | FAIL, 1 failed: mcp | FAIL, 1 failed: mcp | FAIL, 1 failed: mcp |

The trap (a re-entrant kernel loop, not a reset) is gone. The row now reaches
every previously-unreachable step and fails on the SECOND defect instead:

```
[mcp] probe m3f me-method self-field READ ok (miss, as expected)
[mcp] probe m4 register ok
[mcp] probe m5 AuthorityToken.root_for ok
[mcp] response {"status":"ok","body":"MC
[mcp] response {"status":"error","code":"unregistered_tool", ...}
[mcp] FAIL registered dispatch lost the payload
```

This is byte-for-byte the controlled experiment's output, now produced by a
compiler fix rather than a source annotation.

### Regression tests

`native_project/tests.rs`:
`test_build_import_map_records_class_inline_static_factory_return_type` and
`test_build_import_map_records_struct_inline_method_return_type`. Both FAIL
before the `imports.rs` change (`left: None`) and pass after. The struct test
also covers `me get`, another name in the `is_bare_builtin_collection_method`
shadow set, so the defect-class neighbour is pinned too.

### Scope of the TypeId upgrade

Gated on `ty == TypeId::ANY`, so an authored type is never overridden; the only
bindings it can affect are ones that were already erased. Every such site is one
where an erased receiver was being routed to a builtin instead of its user
method — i.e. the defect class itself. The latent mis-resolution the record
notes on x86_64 and aarch64 (where `rt_find` answers `-1` instead of trapping)
is closed by the same change.

### Still open: defect 2

The `.bytes()` / `_bytes_text` truncation (`body":"MC`) is unchanged and is now
the only thing keeping the mcp row red. The record's provenance question stands:
`rt_string_bytes` is not defined in the winning freestanding TU
(`freestanding_runtime.c`), so `.bytes()` is served by a translation unit that
may not share this runtime's array/string layout. That investigation was not
started here.

---

## Defect 2 FIXED — 2026-09-01. Row GREEN, 4 of 4.

```
PASS — 4 component(s) checked (mcp,devtool,caret,testrun), each completed a real
round-trip in-guest on SimpleOS riscv64 under real OpenSBI firmware via
-bios fw_payload (no -kernel, no isa-debug-exit), compiled by the RUST SEED
.../src/compiler_rust/target/release/simple; 100 serial line(s)
```

```
[mcp] request  tool=echo args=[MCP_RTT_PAYLOAD]
[mcp] response {"status":"ok","body":"MCP_RTT_PAYLOAD"}
[mcp] request  tool=no_such_tool_xyz (must be refused)
[mcp] response {"status":"error","code":"unregistered_tool","reason":"no handler for: no_such_tool_xyz"}
COMPONENT_MCP_SIMPLEOS_RISCV64_OK dispatch round-trip echoed the payload and refused the unknown tool
```

### FIRST: the TU-provenance question in this record is answered, and its answer
### was wrong

This record states twice that "the winning TU for this lane is
`freestanding_runtime.c`" and that `rt_string_bytes` and `rt_find` "come from
the hosted runtime". **Both are false.** Measured with `nm` over the retained
link objects (`.simple/native-objects-*/`):

| symbol | defining object(s) |
|---|---|
| `rt_string_bytes` | `_boot_baremetal_runtime_core.inc.o` (T) — and nothing else |
| `rt_index_get` | `baremetal_runtime_core.inc.o`, `baremetal_stubs.o`, `ghdl_boot_info_runtime.o` |
| `rt_string_concat`, `rt_array_len`, `rt_array_get`, `rt_string_len` | `baremetal_runtime_core.inc.o` (+ `baremetal_stubs.o`) |

`_boot_freestanding_runtime.o` defines **none** of them. The hosted
`runtime_native.c` is not on this link line at all. The winning TU is
`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c`.
Correct this before relying on any provenance claim above.

### The defect: raw byte slots collide with TAG_INT == 0

`rt_string_bytes` was ported into `baremetal_runtime_core.inc.c` storing **RAW**
bytes, carrying over the hosted BUGFIX note at `runtime_native.c:2757` ("a `[u8]`
element read truncates with `& 0xFF` WITHOUT untagging"). That note is true
hosted and **false on this lane**.

This runtime uses `TAG_INT == 0`, and every reader untags with the
`IS_INT(v) ? DECODE_INT(v) : v` rule that `simpleos_raw_or_encoded_int` spells
out. So a raw byte whose value is a multiple of 8 is bit-for-bit
indistinguishable from an `ENCODE_INT`-tagged int and is silently **divided by
8** — while the other 224 byte values pass through untouched. That is why the
symptom looked like corruption-after-position-2 rather than a systematic
encoding error.

### In-guest measurement (temporary probes, since removed)

```
[mcp] probe b0  bytes len EXPECTED       # .bytes().len() == 15, correct
[mcp] probe b0a elem0 EXPECTED           # pb[0] == 77 ('M'), correct
[mcp] probe b0c elem2 WRONG              # pb[2] == 10, not 80 ('P')
[mcp] probe b0d elem14 EXPECTED          # pb[14] == 68 ('D'), correct
[mcp] probe b0e cfc80=P END              # char_from_code(80) is fine
[mcp] probe b1  rebuilt=MC
_RTT_
AYLOAD END
[mcp] probe b1a rebuilt len EXPECTED     # 15 chars — RIGHT LENGTH, WRONG BYTES
```

In `MCP_RTT_PAYLOAD` exactly the two `P` bytes (80) are multiples of 8, and both
came back as 10 — i.e. `'\n'`. `_bytes_text` rebuilt `"MC\n_RTT_\nAYLOAD"`, and
`serial_println` stops at the first `\n`, which is the whole of the record's
`body":"MC` and of `[mcp] FAIL registered dispatch lost the payload`.
`.bytes()` length, `char_from_code`, `rt_string_concat` and string interpolation
were all separately probed and are all correct — the probe also compared a
hand-built concat envelope against an interpolated one and both truncated
identically, which is what excluded the builder/interpolation path.

Note the earlier "embedded NUL" reading in this record was wrong: the byte is
`\n`, not NUL, and the serial writer is line-oriented.

### Fix

One line in `baremetal_runtime_core.inc.c`'s `rt_string_bytes`: push
`ENCODE_INT((int64_t)(uint8_t)s->data[i])` instead of the raw byte. This also
makes the port agree with the rest of this arch tree, which already tags —
`freestanding_runtime.c`'s `rt_text_to_bytes` pushes `rt_int(byte)`, and
`rt_bytes_from_raw` documents its slots as "tagged int (byte << 3)". The
consumer `rt_bytes_to_text` already accepted either form, so nothing downstream
changed.

### Reproduce guard

`scripts/check/check-freestanding-byte-array-slot-tags.shs` — fail-closed,
`--selftest` (10 fixtures) runs before every scan and is fatal, same verdict
convention as the other guards, 0 definitions is ERROR. Verified against the
real file: **FAIL on the pre-fix content naming
`baremetal_runtime_core.inc.c:rt_string_bytes`, PASS after**. Modelled on the
sibling `check-freestanding-rt-value-int-tags.shs`, which pins the same tag
class for `rt_value_int`.

Two of its fixtures exist because two earlier revisions of the guard were
**green on the exact content they were written to catch**, and both traps are
worth knowing before writing another guard of this kind:
* **comment masking** — the incident's own body carries the words
  "deliberately NOT ENCODE_INT", so a text match over raw source calls it
  tagged. The guard strips C comments first.
* **the length argument** — the body opens with
  `rt_array_new(ENCODE_INT(s->len))`, so "body contains ENCODE_INT" is true of
  the defective version. The guard classifies the STORE EXPRESSIONS only.
A third fixture pins a pure delegation (`return rt_bytes_alloc_packed(size);`),
which stores no slot and must not be classified — the first run of the guard
reported a false FAIL on x86_64 `rt_extras.c` for exactly that shape.

---

## A THIRD defect was in front of this one: the riscv64 component kernel did not link

Measured 2026-09-01 on a fresh seed at **`origin/main`** as well as at PR #219's
branch — identical, so it is pre-existing and not introduced by #219:

```
Build failed: link failed: ld.lld: error: undefined symbol: rt_mutex_new
ld.lld: error: undefined symbol: rt_atomic_int_new
ld.lld: error: undefined symbol: rt_thread_local_new
```

Exactly three, and they are a consequence of
`60f4cfd8e2d fix(riscv64): freestanding boot never ran module-global
initializers (#209)`: with the `__module_init_*` functions now LIVE, the
module-level globals that construct a mutex, an atomic counter and a
thread-local slot are no longer discarded by `--gc-sections`. The lane runs in
`DeferToLinker` mode, so it failed closed rather than stubbing them to nil —
correct behaviour, and the reason this was a hard blocker rather than a silent
wrong answer.

Fixed by porting exactly those three constructors into
`baremetal_runtime_core.inc.c` (ports of existing hosted names:
`runtime_native.c:3988`, `runtime_native.c:676`,
`compiler_rust/runtime/src/value/sffi/sync.rs:128`). Only three, deliberately —
the same policy the dictionary block in that file already states: the
load/store/lock/unlock siblings are pinned down by no caller in this link, and
if one is ever reached it fails closed at link time with a named undefined
symbol rather than silently returning a wrong value. `rt_atomic_int_new`
returns a RAW pointer handle because the hosted version does
(`(int64_t)(intptr_t)value`, read straight back by `rt_atomic_int_load`);
`rt_mutex_new` returns a tagged heap handle; `rt_thread_local_new` hands out a
monotonic id from 1. The image is single-hart with no preemption in these paths,
so the state is plain memory.

Evidence: link fails at both `origin/main` and the PR #219 branch before the
change; after it, `PASS — riscv64 component-sanity kernel built by the RUST
SEED ... kernel.elf (289776 bytes ELF) + kernel.Image (156344 bytes ...)`.

## Status

All three defects on this row are now closed and the row is **4 of 4**.
