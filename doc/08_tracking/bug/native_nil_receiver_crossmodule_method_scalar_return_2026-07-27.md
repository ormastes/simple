# Bug: cranelift AOT mis-tags the return value of a cross-module struct method returning a primitive scalar

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

- **Filed:** 2026-07-27
- **Lane:** BB2 (board-build, team BOARD)
- **Severity:** HIGH — **silent wrong value**, not just a crash. `x as i64` yields `0`
  instead of the real value, with no diagnostic. The crash is the lucky case.
- **Layer:** compiler `20.hir` / `30.mir` method resolution (`MirLowering.resolved_call_hir_return_type`),
  cranelift AOT backend (`native-build --backend cranelift`)
- **Affects:** every `--mode one-binary` native build. Arch-independent
  (reproduced identically on `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`).
- **Does NOT affect:** the interpreter (`bin/simple run`), which is correct in every case below.

## Symptom

Native binaries die with:

```
runtime error: field access on nil receiver
```

The first observed victim was the SimpleOS TTY/termios path. `build/board_check/feature_check_x86`
prints 13 `PASS` lines and then dies at the first TERM check:

```
PASS tuf.snapshot.mismatch-rejected
runtime error: field access on nil receiver
```

The same source under the interpreter is `board-feature-check: ALL GREEN` (24/24).

## Root cause

A struct method **defined in a different module from its call site**, whose return type is
a primitive scalar (`i32`, `i64`, `u32`), returns a value with a **wrong runtime tag** in
cranelift AOT. The payload is correct; the tag is not. Consequences:

- `.to_text()` prints `<value:0x1>` instead of `1`
- `as i64` silently yields `0`
- using it as an array index yields `nil` → the next field read is the reported
  "field access on nil receiver"

The defect is in **method resolution by flat name**: when a method of the *same name*
also exists in the calling module, resolution succeeds and the return type is recovered,
so the bug disappears. Rename the local method and it comes straight back (probe L vs probe M
below — this is the decisive control).

Cross-module **free functions** are unaffected. Same-module **methods** are unaffected.
Genericity is irrelevant (a non-generic cross-module struct reproduces it identically).

Corroborating compiler diagnostic seen on adjacent inputs:

```
[mir-lower] WARNING: unresolved method call 'to_text' lowered to const-0 placeholder (silent-null risk, Task #145)
```

...and the compiler itself faults in exactly this resolver when it goes wrong
(`gdb` backtrace of a `native-build` SIGSEGV at `si_addr=0x100000000`, i.e. `1 << 32` —
a 32-bit payload used as a pointer):

```
#0  hir__hir_types__SymbolTable_dot_get_symbol ()
#1  mir___MirLoweringExpr__expr_dispatch__MirLowering_dot_resolved_call_hir_return_type ()
#2  mir___MirLoweringExpr__expr_dispatch__MirLowering_dot_lower_expr ()
#3  mir___MirLowering__function_lowering__MirLowering_dot_lower_block_expected ()
...
#7  driver__driver_pipeline__CompilerDriver_dot_lower_to_mir ()
```

## Minimal repro

Two files, no `std`, no `os`, no generics required.

`build/board_check/lib_probe/tiny.spl` (the *other* module):

```
struct Tiny:
    v: i64

    static fn new() -> Tiny:
        Tiny(v: 7)

    fn as_i32(self) -> i32:
        1

    fn as_i64(self) -> i64:
        1

    fn as_u32(self) -> u32:
        1u32

fn free_i32() -> i32:
    1

fn free_i64() -> i64:
    1
```

`build/board_check/probe_m.spl` (call site; `Local` methods deliberately have
names that do **not** collide with `Tiny`'s):

```
use build.board_check.lib_probe.tiny.{Tiny, free_i32, free_i64}

struct Local:
    v: i64

    static fn new() -> Local:
        Local(v: 7)

    fn loc_i32(self) -> i32:
        1

    fn loc_i64(self) -> i64:
        1

fn main() -> i64:
    var lo = Local.new()
    print("l0 SAME-module method i32 =" + lo.loc_i32().to_text())
    print("l0 SAME-module method i64 =" + lo.loc_i64().to_text())
    print("l0 SAME-module i32 as i64 =" + (lo.loc_i32() as i64).to_text())

    var t = Tiny.new()
    print("l1 CROSS-module method i32 =" + t.as_i32().to_text())
    print("l2 CROSS-module method i64 =" + t.as_i64().to_text())
    print("l3 CROSS-module method u32 =" + t.as_u32().to_text())
    print("l4 CROSS-module free   i32 =" + free_i32().to_text())
    print("l5 CROSS-module free   i64 =" + free_i64().to_text())
    print("l6 CROSS-module i32 as i64 =" + (t.as_i32() as i64).to_text())
    return 0
```

### A/B — interpreter vs native (probe M)

| line | construct | interpreter | native (cranelift AOT) |
|---|---|---|---|
| l0 | same-module method `-> i32` | `1` | `1` |
| l0 | same-module method `-> i64` | `1` | `1` |
| l0 | same-module `as i64` | `1` | `1` |
| l1 | **cross-module method `-> i32`** | `1` | **`<value:0x1>`** |
| l2 | **cross-module method `-> i64`** | `1` | **`<value:0x1>`** |
| l3 | **cross-module method `-> u32`** | `1` | **`<value:0x1>`** |
| l4 | cross-module free fn `-> i32` | `1` | `1` |
| l5 | cross-module free fn `-> i64` | `1` | `1` |
| l6 | **cross-module `as i64`** | `1` | **`0`** (silent wrong value) |

### The decisive control (name-collision rescue)

`build/board_check/probe_l.spl` is byte-identical to probe M **except** the local
methods are named `as_i32` / `as_i64` — the same names as `Tiny`'s. With the names
colliding, `l1` and `l2` become **correct** (`1`) natively, and only `l3` (`as_u32`,
which has no same-module counterpart) stays broken. That is what pins the defect to
resolution-by-flat-method-name rather than to calling convention or scalar width.

### Real-code repro (the original victim)

`build/board_check/probe_i.spl` uses the real `std.ecs.component_store.ComponentStore<T>`:

| line | interpreter | native |
|---|---|---|
| `i0 len=` (`ComponentStore.len() -> i32`) | `2` | **`0`** |
| `i1 slot0 raw=` | `0` | `0` |
| `i3 dense[s0].lflag=` | `10` | `10` |
| `i4 slot1 raw=` (`get_slot() -> i32`) | `1` | **`<value:0x1>`** |
| `i5 slot1 as_i64=` | `1` | **`0`** |
| `i6 dense[s1].lflag=` | `11` | **`runtime error: field access on nil receiver`** |

Note slot `0` survives by luck (a mis-tagged zero still indexes to 0), which is why
the failure looks intermittent and why `probe_e` (slot 0) passed while `probe_f`
(slot 1) crashed.

The affected declarations are `src/lib/nogc_sync_mut/ecs/component_store.spl`
`fn get_slot(self, e: Entity) -> i32` and `fn len(self) -> i32`, consumed from
`src/os/services/tty_service.spl` (`self.world.termios.get_slot(tty)` then
`self.world.termios.dense[slot]`).

## Exact commands

Build (fresh `--cache-dir` per attempt — native cache poisoning is a known landmine):

```
env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build \
  --backend cranelift --target x86_64-unknown-linux-gnu --mode one-binary \
  --source src --source build/board_check \
  --entry-closure --entry build/board_check/probe_m.spl \
  --cache-dir build/board_check/nc_probe_m -o build/board_check/probe_m.bin
```

Run the A/B:

```
bin/simple run build/board_check/probe_m.spl     # correct
./build/board_check/probe_m.bin                  # wrong
```

Helper used for all A/B builds in this lane: `build/board_check/ab.shs <entry.spl> <out> <triple> [extra...]`.

## Blocker found while filing this (separate, environmental)

`build/native_probe/simple` (the Jul 23 probe compiler) can no longer `native-build`
**anything**, including hello-world — deterministic 0/6, SIGSEGV at `si_addr=0x100000000`
in `SymbolTable.get_symbol` (backtrace above). It worked at 12:11 the same day. The
mandated default tool `bin/simple` is unaffected and was used for every result here.
Anyone still scripting `build/native_probe/simple native-build` should switch to `bin/simple`.

Minor hygiene defect noticed in the same trace: `src/runtime/runtime_native.c:6207`
redirects subprocess stderr to the **fixed shared path** `/tmp/simple_core_process_run_stderr`,
which races across concurrent `simple` processes. The file is never read back, so it is
not the cause of any failure above, but it should be made per-process (mkstemp).

## Suggested fix direction

Make cross-module method call resolution carry the callee's declared return type into
MIR (qualify the method key by owning module/type instead of the flat name), and make
`resolved_call_hir_return_type` **fail loudly** instead of falling through to an
untagged/placeholder value. The current silent fallthrough is the same
"silent-null risk" already tracked as Task #145.

## Repro assets

All under `build/board_check/`:

| file | role |
|---|---|
| `lib_probe/tiny.spl` | minimal cross-module callee |
| `probe_m.spl` | **primary minimal repro** (distinct local names → broken) |
| `probe_l.spl` | control: colliding local names → rescued |
| `lib_probe/genstore.spl`, `probe_j.spl` | cross-module generic store repro |
| `lib_probe/plainstore.spl`, `probe_k.spl` | cross-module NON-generic control (also broken → genericity irrelevant) |
| `probe_g.spl`, `probe_h.spl` | same-module generic/non-generic controls (both pass natively) |
| `probe_i.spl` | real `std.ecs.ComponentStore` repro |
| `probe_b/d/e/f.spl` | original TTY narrowing probes |
