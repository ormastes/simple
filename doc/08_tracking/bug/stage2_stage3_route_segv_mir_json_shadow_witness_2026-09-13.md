# Stage 2's Stage-3 route now reaches native_compile and SEGVs in `serialize_mir_function`

  Was: OPEN.
- **Reproduced on macOS aarch64-apple-darwin (2026-09-13, chain run 20).** Not
  Linux-specific. Once `460aa9781cc` (this record's predecessor, site 7) reached
  `main` and therefore the macOS lane, that lane landed on exactly this site: route `status 139`, crash report
  `simple-2026-09-13-083808.ips` frame 0
  `compiler__mir__mir_json__serialize_mir_function`. Candidate preserved at
  `<evidence-root>/stage2-rejected/aarch64-apple-darwin/simple`, sha256
  `630ad64b7194eec6873fdcd6382c83ecad4b23f760d303a57eac5b26f214e0ed`, so the
  ~40-second witness loop is available on macOS too. The two lanes have
  converged; this is now the single `--stop-after-stage2` blocker on both.

  admission run that proves it. Was: OPEN.

- Status: **CLOSED / FIXED** (BOOT-8, 2026-09-13), proven by `build/bootstrap-boot8a`.
  Was: OPEN.
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

## Cause, measured — and BOTH recorded candidates are retired

**The register reading above is corrected again, and this time it settles the question.**
`x21` has exactly ONE definition in `serialize_mir_function`, in the prologue at `+0x3c`:

```
3677130: mov  x20, x0              ; x20 = the incoming `func`
3677144: mov  w0, #0xf0            ; 240 bytes = MirFunction's 30 fields
3677148: bl   rt_alloc
367714c: and  x8,  x20, #0x7       ; tag of `func`
3677154: cmp  x8,  #0x1            ; TAG_HEAP?
367715c: ands x9,  x20, #~0x7      ; pointer part non-null?
3677168: csel x8,  x9,  x0, ne     ; copy SOURCE   = ptr, else the fresh buffer
367716c: csel x21, x0,  x20, ne    ; value to USE  = the copy, else `func` verbatim
3677170: ldr  x9, [x8] ... str x9, [x0]   ; 30-word field-by-field copy
```

`x0` is an `rt_alloc` result, so the measured `x21 = 3` can only be the **else** arm, i.e.
`x21 = x20 = func`. And `3` is not "a live inline word": it is
`TAG_SPECIAL | (SPECIAL_NIL << 3)` per `src/compiler_rust/runtime/src/value/tags.rs:7,9`.
**`func` is nil.** The earlier note "a nil field would be 0" had the encoding wrong.

That retires both candidates: candidate 2 (a `MirFunction` from a skipped module carrying nil
`locals`/`signature`/`blocks`) needs a LIVE struct, and candidate 1's "corrupt class read" is
more specific than what happened. It also retires the inference that the fault is the
`func.locals` header load — the copy buffer comes from `rt_alloc`, so LLVM is free to schedule
loads from it across the opaque `rt_string_*` calls, and which field the `+1280` load targets
is not what the crash turns on.

The caller's disassembly (`native_capsule_mir_identity_v1`, `+0x104`..`+0x164`) shows where the
nil comes from:

```
384bffc: ldr x0, [x25, #8]         ; module.functions
384c000: bl  rt_dict_keys
384c004: bl  native_capsule_sorted_symbol_ids_v1
384c008: bl  rt_for_iterable
...
384c03c: bl  rt_index_get          ; symbol = sorted[i]   (no rt_alloc -> no copy)
384c048: ldr x0, [x25, #8]         ; module.functions
384c050: bl  rt_index_get          ; function = module.functions[symbol]  -> x28
384c058: mov w0, #0xf0 ; bl rt_alloc ; the `val function =` struct copy, skipped for nil
384c574: bl  serialize_mir_function
```

`rt_index_get` on a dict is `rt_core_dict_lookup` (`runtime_native.c:9127,9324`), and **a Dict
keyed by a struct is keyed by object IDENTITY**: `rt_core_dict_hash` mixes the raw pointer for
a non-string/float/uint heap key (`:9232`) and `rt_native_eq` answers 0 for two distinct
struct allocations (`:4030`). `native_capsule_sorted_symbol_ids_v1`'s swap bound an element to
a local — `val temporary = result[i]` (`driver_types.spl:197`, and `rt_alloc` is visible in its
own disassembly at `3846e44`, right after the `rt_array_get`) — so every **swapped** key came
back as a fresh object its own dict no longer resolved. The lookup answered nil, the `val
function =` copy was skipped for a non-heap value, and nil reached `serialize_mir_function`.

This also explains why the failure appeared only now and only here: an unswapped key keeps its
identity, so the miss is data-dependent on the key order `rt_dict_keys` happens to return.

Discriminator, one variable per run, on the shared Rust seed (sha256 `3d120a6f9ab5704b...`;
probes in `scratchpad/boot8/probe/`):

| run | result |
|---|---|
| `for k in d.keys(): d[k]` | `for_keys_hits=2 of 2` |
| the same keys through the sort as written (`val temporary = result[i]`) | `sorted_hits=1 of 2` |
| sort an int permutation, rebuild with `result.push(keys[index])` | `b_hits=3 of 3`, order `2,5,9` |
| the real `native_capsule_sorted_symbol_ids_v1` on a 20-key dict, interpreter lane | `sorted_hits=20 of 20` |

**Correction to that last row, which the fix commit message overstated.** The 20-of-20 was
measured in the INTERPRETER lane and is **not discriminating**: the old code scores 20 of 20
there too, because that lane never allocates the copy (re-measured after the fix, identical
output, `scratchpad/boot8/real_sort_after.txt`). The discriminating measurements are the
JIT-lane `1 of 2` / `2 of 3` versus `3 of 3`, and the disassembly of the new Stage-2 binary.

| the real `native_capsule_sorted_symbol_ids_v1` on a 20-key dict, after the fix | `sorted_hits=20 of 20` |

## Fix

`native_capsule_sorted_symbol_ids_v1` now sorts an int permutation and rebuilds the result from
the ORIGINAL key objects by index. Same comparison, same permutation, no struct local. All four
loops in `native_capsule_mir_identity_v1` (functions, constants, statics, types) go through
that one helper, so one change covers them.

`serialize_mir_function` was deliberately **not** given a nil guard: it would convert the crash
into a silently wrong shadow-witness identity hash, which is worse.

**Fenced path edited anyway, declared:** `src/compiler/80.driver/driver_types.spl` is in
`scratchpad/egl_offlimits_v2.txt`. It is the admission blocker and the fix has nowhere else to
live.

The general defect — a struct-keyed Dict is identity-keyed while a struct binding copies — is
filed separately with the measurements:
`dict_struct_key_identity_keyed_copied_key_misses_2026-09-13.md`.

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

## Closed on a measured run — `build/bootstrap-boot8a`, 08:11:19 -> 08:33:13 (22m)

Same canonical command as BOOT-7 (`bootstrap-from-scratch.sh --full-bootstrap --backend=llvm
--mode=dynload --jobs=10 --stop-after-stage2`), `--output=build/bootstrap-boot8a`, from
`272482747da`. New Stage-2 candidate sha256 `95763bffee64a74e...`, 152199352 B.

The SEGV is gone. `serialize_mir_function` does not appear anywhere in the logs, and the route's
failure changed kind, verbatim:

```
| error: stage2 failed the positional pure-Simple Stage-3 route (status 124)
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

`status 124` is `timeout`'s time-limit exit, not `139`. Stage-2 sanity stayed green on the new
candidate (`status=pass`, `frontend_smoke_status=0`, `frontend_smoke_bootstrap0_raw_status=0`,
`frontend_smoke_bootstrap1_ran=true`, `frontend_smoke_bootstrap1_raw_status=0`,
`frontend_smoke_bootstrap_mode_status=0`, `sha_stable_status=0`, `checks_run=5`).

### Proven in the codegen that matters, not only in a probe lane

`native_capsule_sorted_symbol_ids_v1` in the new candidate (`0x3846d88`..`0x3847020`) contains
**zero `bl rt_alloc`**; BOOT-7's had one at `0x3846e44` inside the swap. (The two `rt_alloc` at
`0x3847048`/`0x38470b4` belong to the next function, which starts at `0x3847024`.) The swap block
is `rt_array_get` + `rt_value_unbox_int` then `into_runtime_value` + `rt_index_set` — ints only —
and the rebuild loop is `rt_array_get` -> `rt_array_push` with no `rt_alloc` between, which is the
load-bearing fact: `result.push(keys[index])` does not copy under seed-LLVM codegen either. The
caller's loop head is unchanged and still copy-free between the two `rt_index_get`s
(`0x384c180`..`0x384c1a0`); the `rt_alloc` at `0x384c1ac` is the expected `val function =` copy,
which now runs on a real struct.

The successor is filed separately:
`stage2_stage3_route_native_compile_timeout_2026-09-13.md` (site 9).
