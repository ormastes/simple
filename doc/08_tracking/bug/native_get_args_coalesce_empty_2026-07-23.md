# native (entry-closure): get_args() always [] — `?? []` on non-optional extern result emits rt_is_some on a raw SplArray*

- **Date:** 2026-07-23  **Status:** OPEN (diagnosed by disasm, W81 + rLSP3)
- **Severity:** high — argv is empty in every entry-closure native
  (`--version`/`--help`/flag parsing dead; stdio servers unaffected in serve
  loops).

## Evidence (objdump of lib.nogc_sync_mut.io_runtime.get_args, rLSP3)
```
call rt_get_args        ; returns RAW SplArray* (untagged)
call rt_is_some         ; raw ptr fails the Some check
je   -> rt_array_new(0) ; always takes the [] arm
sar  $0x3,%rax          ; untag shift applied to the fresh array
```
Source: `pub fn get_args() -> [text]: sys_get_args() ?? []` where
`extern fn sys_get_args() -> [text]` (NON-optional). The `??` should be
an identity on a non-optional operand but codegen emits an rt_is_some
discrimination against the raw pointer, which never passes.

Note: the emitted call goes to rt_get_args (extern alias of sys_get_args in
the native lane); a C `sys_get_args` bridge was also added to
runtime_native.c (harmless, currently unreferenced).

## Also suspicious
The taken arm applies `sar $3` (untag) to rt_array_new's result while the
extern arm would return rt_get_args' raw pointer unshifted — the two arms
disagree on tagging; audit extern `-> [T]` return-tag conventions.

## Fix direction
- MIR lowering: `x ?? d` where x's declared type is non-optional must be a
  no-op (pass through), never an rt_is_some probe.
- Audit tag convention for extern functions returning arrays (raw SplArray*
  vs <<3 handle) at call sites.

## Repro
W81: entry `val a = get_args(); print a.len()` with extra CLI args → prints 0.
