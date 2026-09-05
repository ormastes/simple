# Loader: interpreter cannot invoke a raw i64 code address (segment mapper positive control stays red)

Date: 2026-08-18. Lane: aspect-dynload.
Binary: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
59645008, 2026-08-18 10:12:23.164167908 +0000 (identical before and after every run below).

## Symptom

`test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl` — 8 examples,
7 pass, 1 fails, honestly and deliberately left red:

```
POSITIVE CONTROL: the mapped code still executes correctly
  x calls each symbol and gets that symbol's own value back
    assert_equal failed: expected 33, got 0
```

## What was actually wrong first (FIXED)

`src/compiler/99.loader/smf_mmap_native.spl` was a **Dict-simulated fake**
despite a header claiming otherwise: `_g_fake_memory: Dict<i64, [u8]>`, and
`native_call_function_0` unconditionally `return 0`. Both `segment_mapper.spl`
and `module_loader_compat.spl` resolve `compiler.loader.smf_mmap_native` to this
top-level file, so the entire "mapped" path was simulated. That fake `return 0`
is exactly the observed `expected 33, got 0`.

Fixed by routing `native_alloc_exec_memory` / `native_write_exec_memory` /
`native_make_executable` / `native_make_rw` / `native_free_exec_memory` /
`native_reloc_write_i32` / `native_reloc_write_i64` / `native_mmap_read_bytes`
to real `rt_mmap_raw` / `rt_mprotect` / `rt_ptr_write_u8` / `rt_ptr_read_u8`
SFFI calls — the same externs already proven under `bin/simple test` by
`native_mmap_byte_read_spec.spl`.

## What remains, and why it is an ENGINE gap not a mapper bug

There is no supported mechanism in this interpreter to invoke a raw `i64` code
address as a function: no working pointer cast (`unsafe: addr as *u8` /
`fn_ptr as fn()->i64` fails to COMPILE under this seed with
`unsupported cast target type: Pointer`), and no `rt_call_*` extern in the C
runtime. An intermediate attempt at the cast form regressed the file from 1/8
to 6/8 failing and was reverted.

This matches an already-documented limitation: `test/02_integration/app/loader_exec_memory_spec.spl:30`
carries `# skip: native exec memory functions require compiled mode (not interpreter)`.

## Why the assertion was NOT weakened

The positive control is the only example proving the loader still produces
RUNNING code rather than merely correct-looking arithmetic. The other 7 examples
(symbol placement at base+offset, three distinct addresses from one mapping,
out-of-segment refusal, negative offset, over-page alignment, one-free-per-segment
unmap, stable segment key) all pass and all test arithmetic or lifecycle. A green
obtained by deleting or skipping the positive control would destroy the only
evidence that matters. Per `.claude/rules/testing.md`, left red.

## Consequence to state plainly

The lane's headline claim — ONE mmap per SEGMENT instead of one per SYMBOL — is
proven as arithmetic and as mapping lifecycle, and the native layer beneath it is
now real rather than simulated, but **execution of the mapped code is NOT proven
in interpreter mode**. It requires a compiled-mode run to verify.

## Fix options

1. Add an `rt_call_ptr_0(addr: i64) -> i64` extern to the C runtime and use it.
2. Make the pointer/fn cast compile so the sibling `loader/smf_mmap_native.spl`
   approach works.
3. Run this spec under compiled mode in a lane that has a compiled binary.

## Addendum 2026-08-19 (lane-aspect-dynload, W4): same gap now also blocks `object_mapper.spl` mapping itself, not just execution

W4 found a second correctness trap in the same defect class as the
`smf_mmap_native.spl` Dict-fake above: `src/compiler/99.loader/object_mapper.spl`
(the root `compiler.loader` package's public surface, re-exported by
`src/compiler/99.loader/__init__.spl:35-39`) defined its OWN `SharedExecMapper`
that computed `address = 4096 + generation*256 + code.len()` and never mapped
any memory, while the real mapper (`src/compiler/99.loader/loader/object_mapper.spl`,
package `compiler.loader.loader.object_mapper`) sat one directory over and was
reachable only by files that imported it directly. Worse: the REAL load-time
JIT path, `src/compiler/99.loader/loader/jit_instantiator.spl:8-12`, imports
`SharedExecMapper`/`JitMapper` from `compiler.loader.object_mapper` (the fake,
top-level package) instead of its own sibling `.object_mapper` (the real one) —
so genuine JIT instantiation was silently getting fabricated, unmapped
addresses.

Fix applied: `object_mapper.spl` now does
`export use compiler.loader.loader.object_mapper.{...}` instead of defining
its own classes, so every consumer of the `compiler.loader.object_mapper` name
(the public facade and `loader/jit_instantiator.spl`) gets the real,
`native_alloc_exec_memory`-backed mapper.

Consequence, confirmed by direct measurement: this hits the exact cast gap
documented above (`(address + offset) as *u8` in
`loader/smf_mmap_native.spl:native_write_exec_memory`, "unsupported cast
target type: Pointer"), because `map_symbol` now goes through real
`native_write_exec_memory`. Both the pre-existing
`test/01_unit/compiler/loader/object_mapper_spec.spl` (6 examples, previously
green against the fake) and the new reproduce spec
`test/01_unit/compiler/loader/object_mapper_no_fabrication_spec.spl` (2
examples) now fail under interpreter mode with that same error — not because
the mapping logic is wrong, but because the interpreter cannot execute the
real native-memory path at all yet. Per the precedent set immediately above
(the loader positive control staying red rather than reverting to a Dict
fake) and `.claude/rules/testing.md`, these are left red rather than reverted
to fabricated addresses. Re-run both specs once fix option 1 or 2 above lands.

## Blocks: join-point patchpoint execution spec (2026-08-19)

`test/01_unit/compiler/loader/joinpoint_patchpoint_execution_spec.spl` is
legitimately RED because of this defect and must stay RED until it is fixed.

* Symptom, measured 2026-08-19 on `bin/simple`
  (`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
  59645008 bytes, 2026-08-18 10:12:23):
  `error: semantic: unknown extern function: rt_call_ptr_0` — a load-time
  semantic error, so the whole module is rejected before any `it` body runs.
  A second missing extern surfaces on the same path:
  `error: semantic: unknown extern function: rt_ptr_write_bytes`
  (used by `native_write_exec_memory`).
* Path: `JoinpointSlotTable.call_through_0`
  (`src/compiler/99.loader/joinpoint_slots.spl`) -> `native_call_function_0`
  (`src/compiler/99.loader/loader/smf_mmap_native.spl:245`) -> `rt_call_ptr_0`.
  The extern is DECLARED at `smf_mmap_native.spl:15`; what is missing is the
  runtime symbol the interpreter can resolve.
* Unblock condition: `rt_call_ptr_0` (and `rt_ptr_write_bytes`) resolvable from
  the interpreter. Then re-run the spec; no spec change is required.
* NOT blocked by this: the address-level acceptance spec
  `test/01_unit/compiler/loader/joinpoint_patchpoint_spec.spl`, which reads the
  patched pointer back out of the mapped page and passes 31/31 checks today.
