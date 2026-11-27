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

## Update 2026-11-05 (late): exact failing step localized on CURRENT sources

Built the seed fresh from current origin/release/1.0.0 (4m20s, cargo cache
warm). Results:

- The 20-line struct-promote probe now PASSES on the fresh seed JIT lane
  (pr1/pr2=true 3/3, no dylib preload needed) — the SmallEvent-class
  manifestation is gone from current sources. The boot2-era binaries still
  fail it, so that half was fixed (or perturbed away) between
  53af1b6f081 and HEAD.
- The REAL SCV cold-init flow still fails identically on the fresh seed
  (same reason_sha=3ea349...). An env-gated step trace in
  compiler_inventory_file_event_cost_v1 (SIMPLE_SCV_FILE_EVENT_DEBUG=1,
  committed with this update) pinpoints the exact step:

    [file-event] read    identity=.../backend_switching.spl nil=false
    [file-event] event-made identity=... nil=false
    [file-event] done    identity=... retained=false ended=true

  Scope begin/pause/end all succeed; the event (a `struct
  CompileSourceEventV1`, i.e. a RAW-tagged block, not a class object) reads
  and materializes fine; `transient_heap_promote_v1<CompileSourceEventV1>`
  returns FALSE on the seed lane (interpreted and pure-Simple unaffected).

Mechanism analysis at the raw-path level: the Rust twin's promote walk
(collections.rs:3154-3184) reads the struct via C `rt_transient_raw_words`
(succeeds: raw table OR C struct-alloc registry), then promotes each
reachable raw ptr via C `rt_transient_raw_promote` (runtime_memory.c:205),
which returns 0 only when the ptr is in NEITHER the raw table NOR the C
struct-alloc registry. Since raw_words and raw_promote share the raw table
and both consult the struct registry, a consistent C-side state cannot
produce words-OK + promote-0 for the same ptr — so the failing ptr is
either (a) a child raw block of the event that raw_words admitted through
one registry but whose promote-time registry state differs, or (b) a raw
block whose words came from a registry that promote does not re-check in
the same way. Distinguishing (a) from (b) needs one more instrumented
cycle: env-gated eprint of the failing `ptr` at collections.rs:3182-3184
plus the two registry membership checks for that ptr.

Repro (fresh seed, ~3 min build with warm cargo cache):
```
cargo build --locked --offline --manifest-path src/compiler_rust/Cargo.toml \
  --profile bootstrap --target aarch64-apple-darwin -p simple-driver
DYLD_INSERT_LIBRARIES=<any bootstrap>/libsimple_runtime.dylib \
  # still required: JIT cannot resolve simple_contract_check from the exe
SIMPLE_LIB=$PWD/src SIMPLE_SCV_FILE_EVENT_DEBUG=1 \
SIMPLE_BUILD_MEMORY_RESERVE_BYTES=536870912 \
SIMPLE_SCV_INVENTORY_COLD_INIT=1 \
<fresh seed> run src/app/cli/native_build_main.spl native-build \
  --entry src/app/sdn_diff_repro/main.spl --emit-object \
  --backend=cranelift --threads 1 --mode dynload \
  --runtime-path src/compiler_rust/target/aarch64-apple-darwin/bootstrap \
  -o build/probe.o
```

## Update 2026-11-05 (night): definitive mechanism — JIT rt-symbol surface binds the preloaded dylib's twins

Instrumented ALL FIVE `return false` exits of the Rust twin's
`rt_transient_heap_promote` (runtime/src/value/collections.rs, env-gated on
SIMPLE_TRANSIENT_RAW_PROMOTE_DEBUG, format strings verified present in the
rebuilt binary via strings(1); the executable's plain `_rt_transient_heap_promote`
disassembles to the Rust twin calling RuntimeValue::heap_type). Result: the SCV
flow still fails with `retained=false` and ZERO debug lines — the executing
promote is NOT the executable's twin.

Why: the seed binary does not export `simple_contract_check`, so JIT-finalize
crashes (cranelift get_address) unless a runtime dylib is preloaded
(DYLD_INSERT_LIBRARIES). With the dylib present, the JIT resolves its runtime
symbols from the dylib — a SECOND, stale (2026-11-04) copy of the runtime —
while the interpreter and the executable's own code use the executable's
current twins. Evidence: the 20-line probe passes with NO dylib (it never
references simple_contract_check, so its rt symbols bind from the executable);
the big native_build program needs the dylib and its event-promote then runs
the stale twin. All five current-source exits instrumented and silent; the
stale twin's behavior is whatever code shipped Nov 4.

Consequences:
- This morning's "dual-implementation split" refinement was the right family;
  the split is not per-symbol link order but JIT-symbol-source: executable
  (no-dylib programs) vs preloaded dylib (any program JIT-compiling a
  contract call).
- The SCV cold-init failure will very likely clear by rebuilding the runtime
  dylib from current sources (or by eliminating the dylib requirement: export
  the contract/check symbols from the seed executable so JIT binds the
  executable's own current twins). The latter is the cleaner fix — one runtime
  copy per process.

Repro note for the next cycle: `cargo build -p simple-driver` (~4 min warm)
plus the dylib assembly step from scripts/bootstrap/bootstrap-from-scratch.sh
(rust-native-all-build + publish), or test the no-dylib path on any program
that JIT-compiles a contract call after the export fix.
## RESOLVED 2026-11-05: macOS seed now exports its runtime symbols (fix landed)

Root cause of the dylib-twin split: `.cargo/config.toml` set
`-Wl,--export-dynamic` only for `x86_64-unknown-linux-gnu` (an ELF flag;
macOS ld64 needs the single-dash `-export_dynamic` and had NO darwin section
at all). The seed executable therefore never exported `simple_contract_check`
etc., forcing the dylib preload, which moved the JIT's entire rt-symbol
surface onto the stale second runtime.

Fix (this PR's sibling commit on work/seed-export-rt-symbols-20261105):
add `[target.aarch64-apple-darwin]` and `[target.x86_64-apple-darwin]`
sections with `-C link-arg=-Wl,-export_dynamic`.

Acceptance evidence (seed rebuilt from this branch, NO dylib preload):
- `nm -gU` on the new binary exports `simple_contract_check` and
  `simple_contract_check_msg` (2 matches; previously 0).
- The SCV cold-init repro (native_build interpreted, sdn_diff_repro entry)
  passes the inventory phase: 44,669 file-events all complete with
  `retained=true` (previously: failure on the first file event), and the
  build proceeds into the compiler phases — the JIT resolves every runtime
  symbol from the executable's own current twins.

## Windows re-verification 2026-11-06: does not reproduce; no pure-Simple fix needed

Status: RESOLVED (root cause was seed-side linkage, fixed by the macOS
`-export_dynamic` cargo-config change above; no defect in
`src/app/compiler_entrypoint/inventory_scratch.spl` or the transient-scope SFFI).

Host: Windows 11, x86_64-pc-windows-gnullvm seed built 2026-11-06 from
`ab9559d4922` (`simple-simdseed-20261106/.../bootstrap/simple.exe`, copied
before use). Tree: `origin/release/1.0.0` @ `475d1983381`, fresh worktree, no
inventory cursor. Command: the record's repro (`SIMPLE_SCV_INVENTORY_COLD_INIT=1
SIMPLE_SCV_FILE_EVENT_DEBUG=1 ... run src/app/cli/native_build_main.spl
native-build --entry src/app/sdn_diff_repro/main.spl --emit-object
--backend=cranelift --threads 1 --mode dynload --runtime-path build/seedrt`),
with no runtime-DLL preload.

Result:
- 44,895 `[file-event] enter` lines, 44,895 `done ... retained=true ended=true`,
  0 `retained=false`, 0 `SCV-E`.
- `inventory-trace-v1 phase=2 query_status=0 query_bytes=6341551 events=44895`;
  `phase=4 reached=3 valid=true generation=1 published=true` (before: the
  record's `phase=4 reached=1 valid=false reason_sha=3ea349...`).
- The run then stayed in the interpreted compiler phases until the 1500 s
  probe timeout (rc=124). That is the known interpreted native_build_main cost,
  not an admission failure.

Regression test: `test/01_unit/app/compiler_inventory_checked_read_spec.spl`
"retains consecutive file events across back-to-back transient scopes" (three
back-to-back file events, each must be retained with its exact digest): 3/3
pass on the same seed. Limit: `simple test` runs the spec on the seed's
interpreter/hybrid path, so this pins the scope sequence contract but is not by
itself a JIT-lane differential; the cold-init run above is the JIT-lane evidence.
