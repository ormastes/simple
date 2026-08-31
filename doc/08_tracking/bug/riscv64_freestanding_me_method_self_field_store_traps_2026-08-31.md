# riscv64 freestanding: a `me` method storing back into its own `self` field traps

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
that type, and reading a field off an element. What is NOT covered by any
passing probe is the remaining operation — **storing the resulting array back
into a `var` field on `self` from inside a `me` method**.

## What this rules out

* Not the `rt_value_int` untagged-index defect (PR #189) — that is fixed and
  live in this kernel (`slli a0,a0,0x3` in the linked `rt_value_int`).
* Not the `rt_index_get` text-subscript defect fixed alongside this record.
* Not array concatenation, in general or for this element type (m3a/m3d).
* Not entry construction, interning, or registry construction (m1/m2/m3).
* Previously ruled out by earlier lanes: defect C1 (module-global initialized
  from a call expression staying nil) and the closure ABI.

## Not yet located

There is no runtime helper to inspect: a grep of the whole riscv64 boot runtime
(`examples/09_embedded/simple_os/arch/riscv64/boot/*.c`, `*.inc.c`) for
`rt_field_set` / `rt_struct_set` / `rt_class_set` / `rt_field_get` returns
nothing, so class field access is direct-offset codegen. That places the next
step in the compiler's freestanding codegen for a `me`-method self field store,
not in the C runtime.

## Reproduce

```
sh scripts/check/check-simpleos-riscv64-components-in-guest-opensbi.shs
grep -a -m 12 '\[mcp\]' build/os/riscv64_components/serial.log
```

The probes are checked in, in `toolchain_components_entry.spl`, so the serial
log names the last call that completed on every future run.
