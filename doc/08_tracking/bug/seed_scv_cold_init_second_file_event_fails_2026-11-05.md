# Seed-lane SCV cold inventory init fails after the first .spl file event (2026-11-05)

Date: 2026-11-05
Lane: seed (Rust) lane, macOS aarch64
Seed: /private/tmp/boot2-20261104/src/compiler_rust/target/bootstrap/simple
(seed built 2026-11-04 from 53af1b6f081, contains 285c714d224 TextSpan fix)
Tree: work/seed-div-probe-20261105 off origin/release/1.0.0 (bba784f076a)

## Symptom

Any seed-driven `native-build` (or running `src/app/cli/native_build_main.spl`
under the seed) on a fresh checkout fails admission with:

```
workarounds: refresh failed: workaround fragment stage failed
SCV-E-ADMISSION: git-event-refresh-failed
```

The git side is healthy: the exact cold-init query
`git --no-optional-locks -c core.quotePath=false ls-files -t --cached
--others --exclude-standard -- src test examples/10_tooling`
returns rc=0 with 6,321,321 bytes in ~1.5 s on the same machine.

## Trace evidence (SIMPLE_INVENTORY_TRACE_ATTEMPT, 16-64 hex chars)

```
inventory-trace-v1 phase=1 ... cold=true expected=e3b0c44... families=7
inventory-trace-v1 phase=4 reached=1 valid=false reason_sha=3ea349...
  returned= generation=-1 published=false query_status=0
  query_bytes=6321321 overflow=false invalid_fields=false
inventory-trace-v1 phase=cost exists_calls=1 read_calls=1 read_bytes=7301
  events=1 hash_calls=5 materialize_calls=0
```

Decisive counters:

- `query_status=0`, `query_bytes=6321321` == the manual ls-files byte count:
  the git enumeration SUCCEEDED; failure is in event processing.
- `read_calls=1 read_bytes=7301`: exactly ONE file was read, and 7301 is the
  exact byte size of `examples/10_tooling/backends/backend_switching.spl`,
  the FIRST `.spl` line of the scoped listing (the listing's first line,
  `examples/10_tooling/README.md`, is not a compilable source and is skipped
  by `compile_source_inventory_path_valid_v1` before any I/O).
- `events=1`, then the refresh returns invalid: the SECOND `.spl` file event
  (`examples/10_tooling/backends/interpreter_modes.spl`, 3878 bytes, exists)
  fails. Its `file_exists` ran (`exists_calls=1`); its read never ran
  (`read_calls` stayed 1).

## Failure site (candidates, all inside the seed lane)

`compiler_inventory_file_event_cost_v1`
(src/app/compiler_entrypoint/inventory_scratch.spl:17) for the second file:

1. `transient_array_scope_begin_v1()` returns false on the second scope
   (first scope's pause/promote/end sequence leaves state on the Rust-lane),
   or
2. the read/`compile_source_inventory_git_event_cost_v1`/pause/promote/end
   for the FIRST file returned nil after materializing its event
   (counters alone cannot distinguish 1 from 2; both leave events=1).

The transient-scope machinery here is Simple-source
(`transient_array_scope_begin_v1` etc. from
compiler.mir._MirLowering.transient_owner_sffi) executing on the Rust seed
runtime, where the workaround store is also broken ("workarounds: refresh
failed: workaround fragment stage failed" precedes every failure; that line
itself is the pre-existing independent seed defect noted in
seed_jit_demotion_textspan_native_build_stall_2026-10-22.md).

## Impact

- Every fresh-checkout seed-lane native-build is blocked (SCV admission is
  mandatory), not just this tree: cold init is the first-build path anywhere
  without a committed inventory cursor.
- Blocks the 2026-10-12 divergence doc's prescribed next diagnostic
  (enum_payload_local_compatible path-fired differential): both the
  seed-native snapshot build and the interpreted native_build_main probe hit
  this admission wall. The path-trace probe itself is committed on
  work/seed-div-probe-20261105 (SIMPLE_ENUM_PAYLOAD_PATH_TRACE=1 in
  enum_constructor_payload.spl).

## Repro

```
cd <worktree at origin/release/1.0.0+>
SEED=/path/to/seed/simple
DYLD_INSERT_LIBRARIES=<seed-bootstrap>/libsimple_runtime.dylib \
  # ^ seed binary lacks dynamic simple_contract_check exports;
  #   without preload the JIT dies first (cranelift get_address panic)
SIMPLE_LIB=$PWD/src \
SIMPLE_BUILD_MEMORY_RESERVE_BYTES=536870912 \
  # ^ machine had 8.2 GiB free vs default 12 GiB reserve
SIMPLE_SCV_INVENTORY_COLD_INIT=1 \
SIMPLE_INVENTORY_TRACE_ATTEMPT=a1b2c3d4e5f60718293a4b5c6d7e8f90 \
$SEED run src/app/cli/native_build_main.spl native-build \
  --entry src/app/sdn_diff_repro/main.spl --emit-object \
  --backend=cranelift --threads 1 --mode dynload \
  --runtime-path src/compiler_rust/target/bootstrap -o /tmp/probe.o
  # ^ runtime-path must be under the checkout root (SCV scope check);
  #   symlink the seed's target/bootstrap into the worktree
```

## Next

Seed-lane owner: instrument `compiler_inventory_file_event_cost_v1` /
`transient_array_scope_begin_v1` on the Rust lane to pick between
candidates 1 and 2 (one env-gated eprint each is enough). If it is the
second transient scope begin, the fix belongs in the Rust seed's
transient-scope state handling (or the workaround-store defect above is
corrupting the scope stack and is the real root).

## Root cause 2026-11-05 (afternoon): seed JIT miscompiles `mut` params to generic externs (Bug #167 class)

Distinguished the two candidates with a minimal probe (begin/pause/promote/end
twice over a small struct, file `scope_probe.spl`, 20 lines) on the three lanes:

| lane | pr1 | pr2 |
|---|---|---|
| seed JIT (native) | **false** | **false** |
| seed interpreted (`SIMPLE_EXECUTION_MODE=interpret`) | true | true |
| pure-Simple `bin/simple` (1.0.0-beta) | true | true |

Per-lane variance is allocation-order sensitive (a variant probe promoting
i64/[text]/[SmallEvent] returned all-true on the seed JIT and false/true/true
interpreted), matching this family's perturbation law.

`rt_transient_heap_promote` (src/runtime/runtime_native.c:3351) returns 0 in
exactly these cases: scope not active/paused (excluded — begin/pause returned
true immediately before), or `rt_core_transient_classify(value)` gives
root_class 0 while `rt_core_is_heap(value)` and the pointer is not a
registered immortal (runtime_native.c:3379-3392 falls to
`ok = root_class == 1 && ...` = false). Scalars and non-heap copies are a
no-op SUCCESS (return 1). So on the seed-native lane the promoted struct
arrives as a NON-TRANSIENT HEAP COPY: promotion is correctly refused.

Mechanism: `transient_heap_promote_v1<T>(mut value: T)`
(src/compiler/50.mir/_MirLowering/transient_owner_sffi.spl:46) binds `mut` by
REFERENCE precisely so the callee prologue cannot make the Bug #167 defensive
copy ("promoted only that fresh copy while the scope-owned original was
freed at scope end and later reused",
doc/08_tracking/bug/transient_promote_struct_param_copy_dangles_2026-10-25.md).
Pure-Simple codegen honors the by-reference binding; the seed JIT evidently
still copies (or mis-tags) the argument, so `rt_transient_heap_promote` sees a
regular-heap duplicate and refuses. This is the same class as the 2026-10-12
divergence (doc/08_tracking/bug/seed_codegen_interp_native_divergence_2026-10-12.md)
— a third, fully isolated symptom site with a 20-line repro.

Consequence chain: seed-native/hybrid lane -> `transient_heap_promote_v1`
returns false -> `compiler_inventory_file_event_cost_v1` returns nil after
materializing the event -> cold SCV init aborts at the first/second .spl file
-> every fresh-checkout seed native-build is refused. The interpreted and
pure-Simple lanes are unaffected, which is why CI's pure-Simple SCV passes
while any seed-driven build on a fresh cache fails.

## Fix direction (seed lane, owner)

Wherever the seed JIT lowers an extern call with a `mut`-class parameter
(generic `T` at minimum), it must pass the caller's exact root (by reference /
no defensive copy) and preserve the value tag. Verify with the probe above:
pr1/pr2 must be true on the seed JIT lane. Suspect area:
src/compiler_rust/compiler/src/codegen/ (extern argument lowering; compare
with how pure-Simple MIR marks mut-class params). The JIT-vs-interpreted
differential on this 20-line probe is the acceptance test.

## Refinement 2026-11-05 (evening): dual-implementation symbol split, not a param copy

Follow-up probes refine the mechanism (the 20-line repro stays deterministic:
seed JIT pr1/pr2=false 3/3; seed interpreted true/true; pure-Simple true/true):

1. `SIMPLE_TRANSIENT_PROMOTE_DEBUG=1` prints NOTHING on the failing JIT lane.
   That debug print lives only in the C copy (runtime_native.c:3394). So the
   promote JIT'd code calls is NOT the C copy — it is the Rust twin
   (runtime/src/value/collections.rs:3081, #[no_mangle]
   `rt_transient_heap_promote`), whose early `return 0` paths (e.g. the
   fail-closed unknown-heap-kind walk below :3129) have no debug print.
2. The Rust twin walks the RUST heap registry; JIT'd code allocates class
   instances through plain-symbol `rt_object_new`, which ALSO exists in both
   runtimes (Rust twin: runtime/src/value/objects.rs:92, #[no_mangle], calls
   `track_transient_heap`; C twin in runtime_native.c). The executable
   exports exactly one `_rt_object_new` (nm); which twin won the link is
   not visible post-link.
3. If the JIT-bound `_rt_object_new` is the C twin, JIT'd class instances
   are invisible to the Rust registry -> the Rust promote walk fail-closes
   -> false on every cycle, exactly as observed; the interpreter allocates
   through in-crate Rust APIs (registered) -> true. No demotion is involved
   (zero engine-demotion lines on the repro).

So the mechanism class is: per-symbol dual-implementation (C vs Rust twin)
linkage split across the JIT boundary — one more facet of the 2026-10-12
divergence family (same source, two runtime implementations disagreeing
data-dependently), NOT an argument-copy ABI defect.

Decisive next check for the owner (minutes, no rebuild): disassemble the
executable's `_rt_object_new` and `_rt_transient_heap_promote`
(e.g. `otool -tvV` / gdb `disas`) and compare against both twins' code, or
ld -map / `nm -m` at build time to see which object file supplies each
plain symbol. Fix direction accordingly: (a) make the linkage uniform — all
plain rt_* symbols resolve to ONE runtime family in the seed binary
(prefer the Rust twins where they exist, since the interpreter and
transient/promote family already use them), or (b) register C-heap objects
with the Rust registry. Acceptance test unchanged: the 20-line probe's
pr1/pr2 must be true on the seed JIT lane.
