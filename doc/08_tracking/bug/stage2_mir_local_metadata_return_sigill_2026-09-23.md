# Stage2 positional route traps when updating existing local metadata

Date: 2026-09-23. Source baseline: `7f4e04d70627a0fee1258a8f751aad5aca9d6959`.
Status: scoped native regression PASS; independent Astra review PASS.

## Cause and correction

The Stage2 positional Stage3-route admission probe compiled
`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl`
until MIR lowering, then trapped. LLDB confirms `udf #0xc11f` at
`MirLowering.remember_local_hir_type+988`, directly after the existing-ID
branch's third `rt_index_set`. The subsequent bare return cannot return a
value, while the method's terminal array push caused the bootstrap producer
to infer a value-returning signature. The append branch instead returns the
array receiver at +616. The seed's `body_produces_value` and method return
inference in `hir/lower/module_lowering/function.rs`, followed by the nonvoid
`Return(None)` trap in `codegen/instr/body.rs`, explain this generated code.

Declare this side-effect-only method `-> ()`. Its implementation and callers
are otherwise unchanged; callers use the method as a statement. Preserve the
backend fail-fast trap. General implicit return inference and earlier
malformed-HirType post-monomorphization warnings remain OPEN.

## Exact diagnostic authority

Evidence worktree:
`/Users/ormastes/simple-tmp/stage3-route-return-20260923`.
Evidence directory: `build/native_probe/stage3-route`.
`trace.lldb`, `trace-exact.log` and `trace-exact.rss.env` retain the positional
command, call stack and full failing-method disassembly. Rejected candidate
SHA-256: `9b0cfc1a99eb9b64826a5bfd7a2e01ac20991f5be6223850f1829ea1c7a999bd`.
The immutable evidence copy lacked execute permission, so a hash-verified
private executable copy was used. Initial `trace.log` records that permission
failure. `trace-executable.log` used the stale live rejected binary
`8db983200ed0b64881a118c016176f8171a279f5e3cb33b8ec93ea8be656352d`;
it is diagnostic history only, not authority for this Stage2 attempt.

LLDB exits zero after recording the inferior trap; that status is not a
compiler PASS. The exact trace sampled 1,956,272 KiB peak process-tree RSS,
including LLDB, with zero observer errors and quiescence.

## Native regression

`test/fixtures/native/mir_local_metadata_return.spl` imports the actual
MirLowering and HIR implementation. There is no modeled replacement body.
The fixture checks insertion, updating the first and second existing IDs,
no duplicated IDs/types, normalized isolation/resource state, and preservation
of the other local's scalar metadata. It does not establish general HirType
payload transport correctness.

Both variants use frozen bootstrap-only producer SHA-256
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`,
under the P0 authority directory
`build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority`.
The LLVM23 environment is `/tmp/simple-llvm23-toolchain/env.sh`.
Build with `SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_LIB=$PWD/src`,
private `XDG_CACHE_HOME=build/native_probe/stage3-route/fixture-xdg`, and:

```sh
"$probe_authority/simple" native-build --backend cranelift \
  --runtime-bundle core-c-bootstrap --runtime-path "$probe_authority" \
  --source src/compiler --source src/lib --entry-closure --threads 2 \
  --cache-dir build/native_probe/stage3-route/fixture-cache --mode one-binary \
  --entry test/fixtures/native/mir_local_metadata_return.spl \
  --output build/native_probe/stage3-route/green
```

Every build/run is wrapped by `process-tree-rss-watchdog.pl` with
`--max-rss-kib=5859375 --interval-ms=100`, a 180-second build or 20-second run
deadline, and `/usr/bin/time -l`. This is sampled enforcement, not a kernel
hard memory limit. The private cache is preserved across red/green builds.

Red: 319 modules, zero failures, strict link PASS; native run emits
`mir-local-metadata-insert-pass` and exits 132. Red executable SHA-256:
`c91095a1b8ba6537c40fae92f6643d8f09a957f9df2c30bdf402c47a753359be`.
Build wall time 68.60s, sampled tree peak 1,188,352 KiB, max process RSS
1,109,966,848 bytes. Red run wall time 0.36s, max RSS 9,306,112 bytes.
The build exceeds the ordinary 1 GB compilation target; this remains an open
performance limitation rather than an accepted target or a claimed regression
caused by the return annotation.

Green: 319 modules, zero failures, strict link PASS; native run exits zero
with both `mir-local-metadata-insert-pass` and
`mir-local-metadata-update-pass`. Executable SHA-256:
`9f6e7ed6aa301519292a7d2679c1269031e3a1ce1d85cbcb9733ba7b7ba5db5c`.
Build wall time 68.72s, sampled tree peak 1,105,568 KiB, max process RSS
1,057,865,728 bytes. Green run wall time 0.36s, max RSS 9,338,880 bytes.
The single samples do not support a speedup or significant regression claim.
The annotation adds no loops, allocations, scans or I/O. Offline
`green-disassembly.log` shows normal return instructions for both paths and
no `udf` in this method. All red/green receipts report observer_errors=0 and
quiescent=1. Two native build cycles were used, with no green reruns.

The existing source-contract expectation now includes the unit annotation.
Its full SSpec execution awaits an admitted compiler/test runner. Working
direct-env audit and executable-spec layout check pass (zero `.spl` specs
under `doc/06_spec`).

Independent Astra-high review found no blocking issue in the exact diff,
statement-only callers, native red/green evidence and disassembly. The review
explicitly limits acceptance to removal of this reproduced return-path trap.
It did not rerun any passing check.

Stage2 admission requires rebuilding the compiler. No Stage2 admission,
compiler-suite, Stage3, general MCP/core verification or publication is claimed
by this focused bootstrap-only regression.
