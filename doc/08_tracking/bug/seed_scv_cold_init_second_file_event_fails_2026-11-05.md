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
