# Stage 2's Stage-3 route now reaches native_compile and SEGVs in `serialize_mir_function`

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-7, `work/bootstrap-full-5-2026-09-12` at `592041db98a`
- Severity: **the current `--stop-after-stage2` admission blocker**, and the successor to
  site 7 (`stage2_module_surface_registry_graph_promotion_failed_2026-09-13.md`, fixed).
- Candidate: `build/bootstrap-boot7b/stage2-rejected/aarch64-unknown-linux-gnu/simple`,
  sha256 `f02b5a4c1310df6e...`, 152198856 B (executable pin:
  `scratchpad/boot7/pin/simple.boot7b.stage2`, same sha).

## The verdict, verbatim

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 139)
Segmentation fault
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Stage-2 sanity is green again (`status=pass`, both `frontend_smoke_bootstrap0_raw_status=0`
and `frontend_smoke_bootstrap1_raw_status=0`, `sha_stable_status=0`, `checks_run=5`) and
`bootstrap_stage2_struct_receiver=PASS`.

## Forward progress is measured, not claimed

With site 7 fixed the route no longer dies in phase 2. `stage2-receiver.log` shows it now
completes `parse`, `hir` (2/2 modules), `monomorphize`, `mir` (2/2) and `native_cache` (2/2),
and dies inside `native_compile` at `elapsed_ms=94426`, `current=compiler.common.module_path_naming`
— six phases further than site 7 reached.

## The crash, exactly

gdb on the pinned candidate replaying the gate's own probe
(`scratchpad/boot7/gdb9.sh`, `gdb_trace9.log`):

```
#0  compiler.mir.mir_json.serialize_mir_function ()            pc = +1280
#1  compiler.driver.driver_types.native_capsule_mir_identity_v1 ()
#2  compiler.driver.driver_aot_native_output.driver_native_shadow_witness_v1 ()
#3  CompilerDriver._compile_to_native_with_backend_session ()
#4  CompilerDriver.compile_to_native ()
#5  CompilerDriver.compile_with_reverse_reference_owner_v1 ()
#6  CompilerDriver.compile ()
#7  app.cli.bootstrap_main.run_native_build_bootstrap ()
```

**Corrected on a second gdb run — the first reading of this was wrong.** `x0 = 8` in the
initial dump is only `rt_alloc`'s size argument, not the faulting base. Disassembling
`+1280` gives `ldr x20, [x24]` with `x24 = x21 & ~7`, immediately after the `"locals":[`
literal is concatenated — i.e. the load of `func.locals`' object header, at
`mir_json.spl:634` (`for local in func.locals:`). The second run pins the base:

```
#0  0x0000000003677630 in compiler.mir.mir_json.serialize_mir_function ()
x21  0x3      3          <- the value being used as `func.locals`
x24  0x0      0          <- x21 & ~7, the faulting address
```

`func.locals` holds the inline word **3**, not a heap pointer — so it is not an array, and
it is not nil either (a nil field would be 0).

## Two candidate causes, NEITHER verified

A wrongly-DECODED field weighs the candidates: 3 is a live inline word, not an absent one.

1. `native_capsule_mir_identity_v1` (`driver_types.spl:390-392`) reads
   `val function = module.functions[symbol]` — a `Dict` **bracket read** whose value is a
   class. CLAUDE.md's Native-Codegen Dict Pitfalls section still lists class-field `d[k]`
   bracket reads among the OPEN native-only gaps. A corrupt/nil `MirFunction` from that read
   would produce exactly this crash.
2. The same log carries
   `[WARN] stage3 bootstrap-flat pipeline active at aot:flat_mir_passes:skipped: MIR lowering,
   borrow-check, and the flat MIR passes are SKIPPED for all but the bootstrap entry module`.
   A `MirFunction` for a skipped module may carry a nil `signature`/`locals`/`blocks`, and
   `serialize_mir_function` (`mir_json.spl:624-653`) guards none of those fields.

Distinguish by printing the field the load at `+1280` targets (disassemble
`serialize_mir_function` around that offset), not by argument.

## Honest note on the site-7 fix

Before site 7 was fixed this route stopped with a clean error at phase 2; it now SEGVs at
native_compile. The failure mode got LOUDER. That is not a regression introduced by the fix:
the same SEGV was already reachable before it, and this is now backed by a backtrace rather
than by a bare exit code. Running the probe against the PRE-fix candidate
`3ad6fc2a0ac80727...` with `SIMPLE_STAGE3_STREAMING_SURFACES=0`
(`scratchpad/boot7/gdb10.sh`, `gdb_trace_prefix_nostream.log`) gives:

```
#0  0x00000000036776e4 in compiler.mir.mir_json.serialize_mir_function ()
#1  compiler.driver.driver_types.native_capsule_mir_identity_v1 ()
#2  compiler.driver.driver_aot_native_output.driver_native_shadow_witness_v1 ()
x21  0x3      x24  0x0
```

Same function, same caller chain, same faulting value `x21 = 3` — only the pc offset within
the function differs, as it must between two different binaries. The phase-2 guard was
standing in front of this crash, not preventing it.
