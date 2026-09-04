# `self` is bound to `false` inside `register_imported_symbol_inner`, aborting every native-build at `hir 0/N`

- **Date:** 2026-09-01
- **Lane:** goal item 2, x86_64 WM host-Vulkan pixel evidence
- **Status:** OPEN — root cause located 2026-09-01, but **UNCONFIRMED AT TIP**: a
  re-measurement the same day on PR #252 (`3b62ae06871`), with `src/compiler`,
  `src/lib`, `src/app` and the seed binary all verified byte-identical to the
  reporting worktree, could NOT reproduce it (all 12 modules lowered, zero
  field-access errors). Read the "Re-measurement" section at the bottom BEFORE
  acting on the root cause above. The live blocker on this lane is the
  diagnostics-transport drop, which is now fixed.
- **Blocks:** `scripts/check/check-simpleos-x86-64-wm-host-vulkan-pixel-evidence.shs`
  (the host GPU daemon cannot be built, so the gate cannot boot)

## Symptom

`native-build` of the SimpleOS host GPU daemon dies immediately after HIR
starts, at `hir 0/230 step 2/6`, with a single error:

```
error: semantic: undefined field 'symbols': cannot access field on value of type 'bool'
```

The error is **unattributable** in the default configuration: the worker also
prints

```
[ERROR] phase 3 FAILED (diagnostics unreadable: error array did not survive transport)
error: native-build failed without diagnostics
```

so the build looks like it failed for no reason. That masking is why this sat
undiagnosed behind what looked like a source-level import problem.

## Root cause (measured, not inferred)

The error is emitted by the **Rust seed interpreter**, not by the compiler
reporting on user source:
`src/compiler_rust/compiler/src/interpreter/expr/calls.rs:1235`.

Running the same build with `SIMPLE_DEBUG_FIELD_ACCESS=1` (a diagnostic gate
already present at `calls.rs:1210`) names the receiver exactly:

```
[field-access-error] field=symbols recv_type=bool recv=false expr=Identifier("self")
  stack=main -> cli_native_build -> compiler_driver_run_compile -> compile
     -> lower_and_check_impl -> lower_parser_module_unstub -> lower_module
     -> resolve_import_symbols -> register_imported_symbol
     -> register_imported_symbol_inner
```

So inside
`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:183`
(`me register_imported_symbol_inner`), the identifier **`self` evaluates to the
bool `false`** rather than to the lowering context. Every later `self.<field>`
hop then fails; `.symbols` is merely the first one reached.

`false` is also the value of that method's **last** parameter,
`materialize_enum: bool`, and of the same trailing parameter on its only caller
`me register_imported_symbol` (line 97) — both take 6 parameters. That
coincidence suggested a receiver/argument slot mis-binding at arity 6.

## What has been ruled out

- **Not an arity bug, and not the chained-self-call shape either.** Two minimal
  fixtures under the same seed both bind `self` correctly and print the real
  receiver:
  1. `me` methods of 3, 5, 6 and 7 parameters, each with a trailing `bool`,
     called externally (`x.m6(...)`);
  2. the *actual* failing shape — a `me`→`me` **chained self-call** at 6
     arguments (`me outer6(...)` calling `self.inner6(a,b,c,d,e,f)`, with a
     struct in the `Span` position and a trailing `bool`), which is exactly how
     `register_imported_symbol` calls `register_imported_symbol_inner`.

  So neither arity nor self-chaining reproduces it in isolation. The trigger
  needs something else present in the real lowering context — it is **not** a
  simple receiver/argument slot off-by-one, and a fix must not be built on that
  assumption.
- **Not the daemon's source.** No `.symbols` field access exists anywhere in
  the 247-file build closure. The failure is in compiler `.spl` executed by the
  interpreted worker.
- **Not a co-compiled symbol collision on this name.** The build reports 15
  `compiler_cross_module_private_symbol_collision` warnings
  (`env_get`, `dir_list`, `shell`, …); `register_imported_symbol*` is not among
  them.
- **Not the `SymbolTable.scopes` bracket read.** `scopes` is a
  `Dict<i64, Scope>` and `hir_types.spl:379/527` guard `current_scope.id` only
  by numeric range, not by Dict membership, so a hole in the dict looked like a
  candidate. Adding a `contains_key` membership test to both guards does **not**
  change the failure — reverted, since an unverified guard is debt.

## Reproduce (~8 min, no 2-hour build needed)

Any entry whose closure imports `std.nogc_sync_mut.io_runtime` directly
reproduces it in a 12-module closure. Put this at `src/app/<tmp>/i_owner.spl`:

```
use std.nogc_sync_mut.io_runtime.{process_run}

fn main():
    print("hello-i")
    return ()
```

and build it with the daemon's own flag set (from `run_daemon_native_build` in
`scripts/check/check-simpleos-qemu-host-gpu-2d.shs`):

```
SIMPLE_DEBUG_FIELD_ACCESS=1 \
SIMPLE_BINARY=$SEED SIMPLE_BIN=$SEED SIMPLE_BOOTSTRAP_DRIVER=$SEED \
SIMPLE_FRONTEND_DELEGATE=$SEED SIMPLE_FRONTEND_DELEGATED=1 \
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_LIB=$PWD/src \
SIMPLE_LINK_OBJECTS=$RP/libsimple_runtime.a \
  $SEED native-build --backend cranelift \
    --source src/app --source src/lib --entry-closure \
    --entry src/app/<tmp>/i_owner.spl \
    --runtime-bundle core-c-bootstrap --runtime-path $RP \
    --cache-dir <fresh> --timeout 900 --output <out>
```

Fails at `hir 6/12` with the error above. **Always run with
`SIMPLE_DEBUG_FIELD_ACCESS=1`** — without it the diagnostic is swallowed.

## Secondary defects found alongside (separate, still open)

1. **Diagnostics transport drops the error array.** `phase 3 FAILED
   (diagnostics unreadable: error array did not survive transport)` turns a
   precise semantic error into `native-build failed without diagnostics`. This
   masked the bug above and should be fixed independently — a build that knows
   why it failed must be able to say so.
2. **`native-capsule-receipt-invalid`. RESOLVED 2026-09-01** (`310ae337782`,
   test `92210d502cc`). A clean hello-world entry clears HIR and then fails with
   `reason: native-capsule-receipt-invalid:app.<mod>`, producing no binary.

   Root cause: `src/compiler/80.driver/driver_aot_native_output.spl` imported
   `file_write_text`/`file_read_text` from **`std.file_system`**, which its own
   header calls "Mock implementations for pure Simple demonstration". The mock
   `file_write_text` is `if path == "" or content == nil: return false` then
   `true` — it writes NOTHING and reports success. The capsule receipt was
   therefore never on disk, and the validator (which is CORRECT) rejected it.

   Confirming evidence in the failing lane's own cache dir
   (`build/repro/cache-f_noreturn/`): the object, `build_cache.sdn` and the
   `.fpc` are present, while **every** file authored through
   `_sffi_file_write_text` — the receipt, `phase.marker`, `.cache_scope`, the
   witness-shadow receipt — is missing. A clean split along exactly that API.

   Why it was "neither confirmed nor refuted": six same-arity `file_write_text`
   definitions exist across the stdlib, and which one binds is decided by the
   seed's co-compiled-collision fallback ("last definition wins" — the failing
   log's own preserved diagnostics name the collision). The wmvk-x86-3 seed
   picks the mock; the simple-main seed picks a real one and builds green over
   identical source. Both prior observations were right.

   Fix: bind to the uniquely-named, rt-backed `file_write_exact` /
   `file_read_nullable` from `std.io_runtime`; read the receipt back after
   writing so a silent no-op fails at the write site as
   `capsule-receipt-write-unverified`; rename the file-local
   `file_write_text`/`file_read_text` shadows in
   `{nogc_sync_mut,nogc_async_mut}/env/config.spl` that carried the
   `(text,text)->()` vs `->bool` signature collision.

   Measured with the wmvk seed on `src/app/repro_hello/hw.spl`:
   parent `BUILD_RC=1`, no binary, 0 receipts → fixed `BUILD_RC=0`, binary runs,
   1 receipt. Reproduce: `sh scripts/check/repro-native-capsule-receipt-invalid.shs`.
   Ratchet: `sh scripts/check/check-no-mock-file-system-io.shs` (baseline 9).

   **Defect-class neighbours, still open (not fixed here):** 9 remaining
   product-code imports of mock `std.file_system` I/O primitives, several in
   `80.driver` (`driver_api_interpret`, `driver_api_project_build`,
   `watcher/smf_manifest`, `cache/lease/lease`, `driver_public_headers`, …), and
   ~13 other same-name/differing-signature stdlib collisions the failing log
   names (`env_get`, `dir_create`, `dir_list`, `file_size`, `shell`,
   `process_wait`, `join_path`, …). Each is the same latent silent-success trap.

   The `self`-bound-to-bool defect (above) remains the lane's first blocker.

## Status of the five PR #252 fixes (calibrated)

This build was launched to confirm or refute them. What the evidence supports:

| # | fix | status |
|---|---|---|
| 1 | `log.spl` nil `env_get` | **confirmed** — the build now reaches step 2/6; previously every native-build aborted during parse |
| 2 | `draw_ir_adv.spl` 3 names | clears parse + surface_build; **HIR pending** |
| 3 | `vulkan_sffi.spl` 10 `rt_vulkan_*` | clears parse + surface_build; **HIR pending** |
| 5 | `backend_session.spl` `alias`→`type` | clears parse + surface_build; **HIR pending** |
| 4 | `rt_env_cwd` re-export | **unconfirmed** |

2/3/5 cannot be called confirmed: HIR died at module 0 of 230, before any of
their modules was lowered.

Fix #4 is **unconfirmed, not refuted**. A small-closure probe importing
`std.env.platform` did report `unresolved name: rt_env_cwd` (and `process_run`,
a *long-standing* export through the same `export X from Y` line that the old
230-module census never flagged) — which points at the small-closure probe
being unfaithful for `export ... from` edges rather than at fix #4 being wrong.
A sibling probe importing `env_get` through the same facade surfaced no
unresolved-name diagnostic; given the diagnostics-transport defect below, that
absence is weak evidence and must not be read as "resolved". Fix #4 needs a
full-closure build to judge.

## Do not re-derive

- The kernel half is **done and green**:
  `sh scripts/os/build-simpleos-x86-64-desktop-engine2d-kernel.shs` builds
  `build/os/simpleos_x86_64_desktop_engine2d.elf` (12,411,968 bytes, x86-64 ELF
  with `.text`), verdict `PASS`.
- The gate's own `--selftest` is green: `PASS — 17 selftest fixture(s) checked`.
- Host GPUs are present and Vulkan-capable (NVIDIA TITAN RTX + RTX A6000,
  Vulkan 1.4), and OVMF/qemu/grub-mkstandalone are all installed, so
  `renderer=host-vulkan` is genuinely reachable once the daemon builds.
- The 101 MB vulkan+cuda `libsimple_runtime.a` must be **reused**, never
  rebuilt (`build/simpleos_gpu_host/x86_64-vulkan-cuda-runtime-target/bootstrap/`).
- `--timeout 1200` is a floor, not a cap: parse + surface_build alone measured
  **7227 s** cold on this closure. Preserve `build/simpleos_wm_vulkan/daemon-cache`
  — it holds that work and makes a rerun far cheaper.

## Re-measurement 2026-09-01 (lane: g2x86-selffix, PR #252 tip 3b62ae06871)

**The `self`-bound-to-bool failure did NOT reproduce on the documented
12-module closure at this tip.** Recorded so the next session does not spend
another cycle re-deriving a defect that may already be absent.

### Inputs verified identical to the reporting worktree (`wmvk-x86-3`)

Ruling out worktree skew before drawing any conclusion — `diff -rq`:

| input | result |
|---|---|
| `src/compiler` | byte-identical |
| `src/lib` | byte-identical |
| `src/app` | byte-identical (except this lane's probe entry) |
| seed binary | same file, `60744944` bytes, mtime `2026-08-26 01:16:25` — predates the 2026-09-01 report, so it is the same seed the reporter ran |

So the compiler source, the stdlib, and the seed are all the ones the original
measurement used. Whatever differs is not the tree.

### What the instrumented run measured

`register_imported_symbol_inner` was instrumented with four `eprint` probes
(entry, and after each candidate clobbering statement in the window between
entry and the first `self.symbols` access). Sentinel satisfied: **4,778 probe
lines fired**, so the seed was demonstrably executing THIS worktree's compiler
source (the nested-`.git`/other-worktree stdlib hazard is excluded by
measurement, not assumed).

Result: **`hir 12/12` completed, and `grep -c field-access-error` = 0.** Not one
receiver was a bool. The documented `hir 6/12` abort did not occur.

### What fails instead, at this tip

All 12 modules lower; the build then dies in phase 3 with the diagnostics
already-filed transport defect and nothing else:

```
[hir-cache] hits=0 misses=12 stores=11
[ERROR] phase 3 FAILED
[ERROR] phase 3 FAILED (diagnostics unreadable: error array did not survive transport)
error: native-build worker exited with code 1.
```

So on this closure the **diagnostics-transport drop is now the primary
blocker**, not a secondary annoyance: the real phase-3 error is unreadable, and
`12 misses / 11 stores` says exactly one module failed to lower cleanly without
naming it.

### Calibration for whoever picks this up

- Do NOT assume the `self`/bool defect is fixed. Two readings remain open and
  are not yet discriminated: (a) it is genuinely absent at this tip, or (b) the
  `eprint` probes perturbed it away (an added statement changes env
  publish/repoint traffic, which is plausible for a receiver-corruption bug).
  A no-probe rerun is the discriminator and must be read together with the
  `[hir-cache] hits=` line — a warm HIR cache makes modules skip lowering
  entirely, so `hir 12/12` with hits > 0 proves nothing.
- `error_message_at()` faulting on a zeroed `self` while `has_errors()` works on
  the *same* receiver (`driver_orchestration.spl:236-258`) is the same
  defect class as this bug — one interpreter receiver-corruption defect wearing
  two costumes. Fixing the receiver bug likely closes both.

## Diagnostics-transport defect: FIXED, with RED/GREEN evidence

Secondary defect 1 above ("Diagnostics transport drops the error array") is
fixed in `src/compiler/80.driver/driver_orchestration.spl` (DIAGREAD).

**It was never a transport failure.** The errors were formed, recorded and
readable the whole time. The failure branch simply declined to read them and
asserted they were lost. Proof, from the same process, same failure, twenty
lines apart in the same function: the `SIMPLE_BOOTSTRAP_DEBUG` block called
`error_message_at` and printed

```
[bootstrap-phase3-errors] count=1
[bootstrap-phase3-error] index=0 len=156 text=HIR lowering error in <entry>:
  untyped function returns a value: function 'main' returns a value but
  declares no return type; add '-> T'
```

while the non-debug branch printed `diagnostics unreadable: error array did not
survive transport`. The accessors (`error_message_at` / `errors_safe`,
`driver_types.spl:1115/1131`) had since been hardened to probe
`rt_heap_ref_wellformed(self.errors)` and return `""` / `[]`, so the hazard the
old comment described was already handled at the callee. The unreadable case is
still covered — it is now DETECTED (empty `errors_safe()`) rather than presumed.

Gate: `scripts/check/check-phase3-diagnostics-reported.shs`
(`--selftest`: `PASS — 5 selftest fixture(s) checked`).

RED at the fix's own parent (`6e91c42c2ee`), verdict verbatim:

```
FAIL — 2 assertion(s) checked, phase-3 diagnostics not reported: build claimed the diagnostics were unreadable instead of reporting them;
```
exit 1.

GREEN at the fix (`26ca3d22efb`), verdict verbatim:

```
PASS — 2 assertion(s) checked, phase-3 diagnostics reported
```
exit 0.

The gate asserts BOTH that the specific diagnostic text appears AND that the
"unreadable"/"without diagnostics" wording does not. Asserting only "the build
failed" would be vacuous: it failed before the fix too, which is precisely how
this defect survived.

### Note on the repro snippet in this document

The 12-module repro entry printed above uses

```
fn main():
    print("hello-i")
    return ()
```

and **that entry does not compile** — `return ()` in a `main` with no declared
return type is itself the HIR error quoted above. Every run of the documented
repro therefore died on the fixture, not on the defect under investigation, and
the transport defect hid which. Drop the `return ()` line before reusing it.

---

## ROOT CAUSE FOUND AND FIXED (2026-09-01, later session)

**Status: FIXED.** The defect is in the Rust seed interpreter's chained
method-call write-back, exactly as the previous session's "corruption is in the
interpreter's env slot for `self`" conclusion predicted.

### The two measurements that closed it

The previous session's recommended step was implemented: print the **local
environment's key set** in the `[field-access-error]` branch, since
`Expr::FieldAccess` carries no span. That named the frame immediately:

```
[field-access-error] field=symbols recv_type=bool recv=false expr=Identifier("self")
  stack=... -> register_imported_symbol -> register_imported_symbol_inner
  locals=alias_position,already_bound,callable_position,composite_position,
         constant_position,enum_position,import_span,imported_index,imported_mod,
         imported_mod_name,imported_name,local_name,materialize_enum,
         routed_origin,scan_started,self,surface_key,trait_position
```

So the failing hop IS in `_inner`'s own frame, `self` IS in that frame's
overlay, and the frame is past the `already_bound` / `*_position` bindings.

A second trap (`SIMPLE_TRAP_SELF_WRITE=1`, on `CowEnv::insert`, printing a Rust
backtrace whenever a **bool** is written into any frame's `self` slot) fired
**exactly once** and named the writer:

```
[self-slot-write] value_type=bool value=false
   0: CowEnv::insert
   1: interpreter::node_exec::exec_node
   2: block_exec::exec_block_fn
   3: interpreter_control::exec_if_core
   ...
   8: interpreter_helpers::patterns::handle_method_call_with_self_update_inner
   9: interpreter_helpers::patterns::handle_method_call_with_self_update
```

`exec_node`'s `Node::Let` arm does `env.insert(obj_name, new_self)` with the
pair returned by `handle_method_call_with_self_update`.

### The defect

`interpreter_helpers/patterns.rs`, the **owned-values** branch of
`handle_method_call_with_self_update_inner`, for a chained call
`root.<inner>(..).<outer>(..)`:

```rust
if let Some((ref obj_name, _)) = inner_update {
    if let Value::Object { class: updated_class, .. } = &updated_inner_self {
        if updated_class == class {                       // <-- always true
            return Ok((outer_result.clone(),
                       Some((obj_name.clone(), outer_result))));   // <-- writes the
        }                                                          //     RETURN VALUE
    }                                                              //     into the ROOT
    return Ok((outer_result, inner_update));
}
```

`class` is the class of the **outer call's own receiver**, and
`updated_inner_self` is that same receiver after the call — so
`updated_class == class` compares a class to itself. It is trivially true and
says nothing about `obj_name`, the ROOT variable being overwritten.

Applied to `module_import_registration.spl`'s
`val already_bound = self.symbols.lookup_or_invalid(local_name).is_valid()`:

- root (`obj_name`) = `self` (the `HirLowering` receiver),
- outer receiver = the `SymbolId` returned by `lookup_or_invalid`,
- `updated_class == class` is `SymbolId == SymbolId` -> passes,
- `outer_result` = `is_valid()`'s **bool** -> `env.insert("self", Bool(false))`.

`self` is a bool from that statement onward, so the next `self.symbols` hop
fails with *"cannot access field on value of type 'bool'"*. `.symbols` is
merely the first field reached — which is why every source-level probe wave
was silent: nothing in `.spl` rebinds `self`, and every method *entry* really
was clean.

### Why six probe waves missed it and the sibling fix did not cover it

The non-owned fallback path ~60 lines below already carries the CORRECT gate —
`inner_self.class == outer_result.class` **and** both links declared `me` —
added by
`doc/08_tracking/bug/chained_method_call_writes_result_back_into_receiver_variable_2026-08-31.md`.
That fix hardened one path and missed its owned-values sibling. The two paths
now carry the identical gate.

### Evidence (12-module reproducer, same seed, same flags, same cache policy)

| | before fix | after fix |
|---|---|---|
| `[field-access-error]` count | 1 | **0** |
| `[self-slot-write]` count | 1 | **0** |
| furthest HIR module | `hir 6/12` (`std.nogc_sync_mut.io.pipe`) FATAL | **`hir 12/12`** |

`SIMPLE_DEBUG_FIELD_ACCESS=1` was set on every measuring run, per this record's
own warning.

### Fixture bug exposed by getting further

With HIR completing, the reproducer entry itself failed on
*"untyped function returns a value: function 'main' returns a value but
declares no return type"* — a defect in `src/app/repro_iowner/i_owner.spl`'s
own `return ()`, unreachable before because HIR never got that far. Removed.
Note the diagnostics **did** survive transport on this run (secondary defect 1
did not reproduce here).

### Diagnostics retained (do not delete — logging retention policy)

- `[field-access-error]` now also prints `locals=` (frame overlay keys) and
  `env_keys=`, gated on the existing `SIMPLE_DEBUG_FIELD_ACCESS`. This is the
  attributability this record complained was missing.
- `SIMPLE_TRAP_SELF_WRITE=1` on `CowEnv::insert` (capped at 8 reports).

### Reproduce test, RED-before / GREEN-after against the fix's OWN parent

`test/01_unit/interpreter/chained_call_self_slot_corruption_spec.spl`
(3 examples) mirrors the failing shape.

The parent seed was built by reverting **only** `patterns.rs` to
`f861a2e42e7~1` into a separate `CARGO_TARGET_DIR`, so the one-file change is
the only variable:

| seed | result |
|---|---|
| fix's own parent (only `patterns.rs` reverted) | **3/3 FAIL** — `undefined field 'tag': cannot access field on value of type 'bool'` |
| with the fix | **3/3 PASS** |
| pre-existing unfixed seed in `wmvk-x86-3` | 3/3 FAIL (same signature) |

Regression check: `chained_call_receiver_mutation_spec.spl` still passes
**5/5** on the fixed seed, including
`it "still writes back a genuine me-method builder chain"` — the case the gate
must keep admitting.

This spec doubles as the methodology sentinel: it discriminates between the two
binaries, so the results cannot be a stale-source / cross-worktree artifact.
`cargo check --release --bin simple` is clean.

### End state of the 12-module reproducer after the fix

Final run (fixture's own `return ()` removed): **`hir 12/12`, 0
`[field-access-error]`, 0 `[self-slot-write]`.** The `self`-bound-to-bool
blocker is gone.

The build still ends `BUILD_RC=1`, but at a **new and different** failure past
HIR:

```
error: semantic: type mismatch: cannot convert enum to int
```

This is NOT the `self` defect and NOT `native-capsule-receipt-invalid`
(that reason string does not appear in this run). It is a newly-reachable
downstream defect that no build had ever got far enough to see. It needs its
own record and is out of scope for this one. Note also that diagnostics
survived transport on every post-fix run, so secondary defect 1
("error array did not survive transport") did not reproduce here.
