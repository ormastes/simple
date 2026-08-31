# riscv64 freestanding: invoking a `me` method on a class instance traps

Status: OPEN
Filed: 2026-08-31
Lane: `scripts/check/check-simpleos-riscv64-components-in-guest-opensbi.shs` (mcp row)
Evidence: in-guest, real OpenSBI v1.4 `fw_payload`, `-bios` only. No `-kernel`, no `isa-debug-exit`.

## Symptom

The gate's `mcp` row traps. The CPU re-enters the entry (the two `[components]`
banner lines reprint) **without a fresh OpenSBI banner** — measured 1 OpenSBI
banner against 14,564+ entry banners — so it is a trap, not a machine reset.

## Localization (this is the new part)

Serial bisect probes were placed between every call in `mcp_component_row`. The
last line printed is `probe m3e`; `probe m4` never appears. Everything before
the trap works:

```
[mcp] probe m0 entering row
[mcp] probe m1 id_path_intern ok
[mcp] probe m2 DispatchEntry.echo ok
[mcp] probe m3 DispatchRegistry.new_for_test ok
[mcp] probe m3a local array concat returned      # ["a"] + ["b"]
[mcp] probe m3b elem=a
[mcp] probe m3b elem=b
[mcp] probe m3c array literal of DispatchEntry ok    # [entry]
[mcp] probe m3d DispatchEntry array concat ok        # [entry] + [entry]
[mcp] probe m3e first tool_name=echo                 # elem field read
<trap>
```

The only statement between `m3e` and `m4` is `reg.register(entry)`, whose whole
body (`src/lib/nogc_async_mut/mcp/dispatch.spl:89-90`) is:

```
me register(entry: DispatchEntry) -> ():
    self.entries = self.entries + [entry]
```

Every ingredient of that line is independently proven working in-guest by the
probes above: array literals of the class element type, array concatenation of
that type, and reading a field off an element.

**A second, discriminating probe settles which remaining operation is at
fault.** `probe m3f` was placed immediately before `register` and calls
`reg.find("no_such_tool_at_all")` — a `me` method on the same instance that
only READS `self.entries` (`for e in self.entries`) and stores nothing. It
prints nothing: `m3f` traps too, exactly like `register`.

So the defect is **invoking a `me` method on a class instance at all**, not the
field store. Note that no row of this gate had ever successfully called a `me`
method in-guest: devtool, caret and testrun reach their evidence through free
functions, static constructors, array `.len()` and plain field reads. The
static constructors (`DispatchEntry.echo`, `DispatchRegistry.new_for_test`) do
work (m2/m3) — those are `static fn`, which take no `self`. The failing shape
is specifically the `self`-receiving method call.

The original title of this record named the self-field STORE; that was the
leading suspect before `m3f` existed, and it is wrong. Kept here so the wrong
inference is not silently re-derived.

## What this rules out

* Not the `rt_value_int` untagged-index defect (PR #189) — that is fixed and
  live in this kernel (`slli a0,a0,0x3` in the linked `rt_value_int`).
* Not the `rt_index_get` text-subscript defect fixed alongside this record.
* Not array concatenation, in general or for this element type (m3a/m3d).
* Not the self-field STORE specifically — a read-only `me` method traps too (m3f).
* Not `static fn` constructors on the same classes, which work (m2/m3).
* Not entry construction, interning, or registry construction (m1/m2/m3).
* Previously ruled out by earlier lanes: defect C1 (module-global initialized
  from a call expression staying nil) and the closure ABI.

## Not yet located

There is no runtime helper to inspect: a grep of the whole riscv64 boot runtime
(`examples/09_embedded/simple_os/arch/riscv64/boot/*.c`, `*.inc.c`) for
`rt_field_set` / `rt_struct_set` / `rt_class_set` / `rt_field_get` returns
nothing, so class field access is direct-offset codegen. That places the next
step in the compiler's freestanding codegen for the `me`-method calling
convention — how the `self` receiver is passed — not in the C runtime.

Suggested next probe: the smallest possible reproduction, a two-line class with
one `me` method that only calls `serial_println` and touches no field. If that
traps, the receiver ABI is the whole story and the reproduction is small enough
to disassemble.

## Reproduce

```
sh scripts/check/check-simpleos-riscv64-components-in-guest-opensbi.shs
grep -a -m 12 '\[mcp\]' build/os/riscv64_components/serial.log
```

The probes are checked in, in `toolchain_components_entry.spl`, so the serial
log names the last call that completed on every future run.
