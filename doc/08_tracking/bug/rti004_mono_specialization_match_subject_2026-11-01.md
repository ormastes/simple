# E-RTI-004 / unresolved binder on mono specializations used as match subjects (2026-11-01)

Status: OPEN in the frozen stage2 bootstrap compiler (`C:/dev/p3new/stage2.exe`,
built 2026-10-27, monomorphization pass present). Worked around in source with
`# @workaround bug=rti004-mono-20261101` (behaviour-identical rewrites).

Owner area: `src/compiler/40.mono` (deleted 2026-10-31, 200a05f5bc8) x
`src/compiler/20.hir/return_type_interface_v1.spl` (RTI symbol lookup) x
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
(`rti_enum_match_subject_type`, local binder typing in specializations).

Phase-3 evidence: `C:/dev/p3new/r11/build.log.err` (`[go-to-end] failed stage=mir`):
- (E) `E-RTI-004: no local symbol for id 1125899906842761..770` x 44 at
  `src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl` lines
  107, 165, 260, 326, 337, 354, 360, 362 and `src/lib/nogc_async_mut/async_ring/async_ref.spl`
  lines 270, 279.
- (F) `lib.nogc_async_mut.async_ring.simple_ring`: `enum match: bare variant 'Ok' is ambiguous
  (declared in multiple enums); qualify it as EnumName.Ok; subject expression at
  simple_ring.spl:383:31 has type unresolved` and `enum construction
  RingCancelOutcome.CancelRejected: payload type mismatch at 0; function=SimpleRing__cancel$i64_i64`.

## Root cause (one bug, two symptoms)

The stage2 monomorphization pass allocates every specialization symbol from
`MONO_SYMBOL_BASE = 1125899906842624` (2^50; deleted
`src/compiler/40.mono/monomorphize_integration.spl:87` at `200a05f5bc8^`). The
failing ids are exactly `2^50 + n` for the `n` specializations the build logs
(`[mono] ... specializations=12` -> ids 2^50+0..11 in the 77-module repro
closure). Those symbols are placed under the *owner* module (see
`doc/08_tracking/bug/mono_specialization_rti_alias_owner_2026-10-30.md`); the
importing module's `SymbolTable.symbols` never receives them.

- **E (importer side).** When a call on a generic-class instance is the
  *subject of a `match`*, MIR asks the ReturnTypeInterface for the scrutinee
  type (`rti_enum_match_subject_type` ->
  `ReturnTypeInterface.callee_return` -> `receiver_owner`). The receiver's HIR
  type is `Named(sym)` where `sym.id` is the specialization id, so
  `rti_type_decl_ref` / `decl_ref_of` (`return_type_interface_v1.spl:264-274`,
  `656-668`) miss `symbols.get_symbol_raw(raw)` and return
  `E-RTI-004: no local symbol for id <2^50+n>`, which the match lowerer treats
  as fatal. Receivers that are a `self.<field>` chain and plain parameters both
  trigger it; a generic free function instantiated explicitly
  (`async_ref_deliver_wake_i64<i64>(..)`) does too. A match over a *typed
  local* never consults RTI (the local's declared type answers), which is why
  the earlier `ctor-mir-20261031` binders on lines 180/296 of the bridge
  already lowered.
- **F (inside the specialization).** Inside the specialized body
  (`SimpleRing__cancel$i64_i64`, `Box__settle$i64` below) an *untyped* local
  initialised from a self call (`val r = self._release_slot(slot)`) stays
  `unresolved` because the same lookup cannot type the callee. A bare `Ok` arm
  over an unresolved subject is then reported as ambiguous, and `Err(error)`
  binds an untyped payload so `RingCancelOutcome.CancelRejected(error)` fails
  with `payload type mismatch at 0`. Qualifying the arms as `Result.Ok` /
  `Result.Err` does **not** fix it (verified: `settle_qualified` below still
  fails); annotating the binder does.

Current `src/compiler` (stage3 source) no longer has the mono pass, so the
2^50 id space cannot be produced there and this exact failure cannot recur in
a stage3 built from `release/1.0.0`. It was not verified by running a stage3
binary (none built in this session); generic calls now lower type-erased per
`doc/08_tracking/bug/monomorphization_deleted_2026-10-31.md`. The RTI lookup
gap itself (`decl_ref_of` only consulting the importer's table) still exists in
source and would resurface with any future specialization scheme that mints
symbols outside the module table.

## Minimal repro (pinned stage2, `compile --format=smf`)

`rti004_box.spl` (module `rti004_box`):

```simple
pub enum ProbeError:
    Bad

pub enum Outcome:
    Fine
    Rejected(ProbeError)

pub class Box<T>:
    value: T

    me probe(flag: bool) -> Result<(), ProbeError>:
        if flag: Ok(()) else: Err(ProbeError.Bad)

    # F: untyped local from a self call inside the generic class -> FAILS
    me settle(flag: bool) -> Outcome:
        val probed = self.probe(flag)
        match probed:
            case Ok(_): Outcome.Fine
            case Err(error): Outcome.Rejected(error)

    # F variant A: qualified arms only -> still FAILS
    me settle_qualified(flag: bool) -> Outcome:
        val probed = self.probe(flag)
        match probed:
            case Result.Ok(_): Outcome.Fine
            case Result.Err(error): Outcome.Rejected(error)

    # F variant B: typed binder -> lowers
    me settle_typed(flag: bool) -> Outcome:
        val probed: Result<(), ProbeError> = self.probe(flag)
        match probed:
            case Ok(_): Outcome.Fine
            case Err(error): Outcome.Rejected(error)

export Box, ProbeError, Outcome
```

`entry.spl`:

```simple
use rti004_box.{Box, ProbeError, Outcome}

class Holder:
    box: Box<i64>

    me via_field(flag: bool) -> i64:        # E: FAILS (entry.spl:9:15)
        match self.box.probe(flag):
            case Ok(_): 0
            case Err(_): 1

fn via_param(box: Box<i64>, flag: bool) -> i64:   # E: FAILS (entry.spl:14:11)
    match box.probe(flag):
        case Ok(_): 0
        case Err(_): 1

fn via_typed_local(box: Box<i64>, flag: bool) -> i64:   # lowers
    val probed: Result<(), ProbeError> = box.probe(flag)
    match probed:
        case Ok(_): 0
        case Err(_): 1

fn use_variants(box: Box<i64>) -> i64:
    val a: Outcome = box.settle_qualified(true)
    val b: Outcome = box.settle_typed(false)
    match a:
        case Outcome.Fine: 0
        case Outcome.Rejected(_): 1

fn main() -> i64:
    val h = Holder(box: Box(value: 1))
    h.via_field(true) + via_param(Box(value: 2), false) + via_typed_local(Box(value: 3), true) + use_variants(Box(value: 5))
```

Command (worktree root, PATH with `C:/msys64/clang64/bin` and the llvm-mingw
`bin`, `CC` = llvm-mingw `clang.exe`):

```
C:/dev/p3new/stage2.exe compile build/repro/rti004_two/entry.spl --format=smf \
  --source src/lib --source src/compiler --source src/app --source build/repro/rti004_two \
  --keep-going --go-to-end
```

Observed (6 s, peak RSS 0.04 GB, `phase=mir state=failed ... failed=2`):

```
MIR lowering error: E-RTI-004: no local symbol for id 1125899906842626 at build/repro/rti004_two/entry.spl:9:15
MIR lowering error: E-RTI-004: no local symbol for id 1125899906842626 at build/repro/rti004_two/entry.spl:14:11
MIR lowering error: enum construction 'build.repro.rti004_two.rti004_box.Outcome.Rejected': payload type mismatch at 0; function=Box__settle$i64 ...
MIR lowering error: enum construction 'build.repro.rti004_two.rti004_box.Outcome.Rejected': payload type mismatch at 0; function=Box__settle_qualified$i64 ...
```

`via_typed_local`, `settle_typed` and every single-file variant (generic class
declared in the entry module itself, one or two type params, field or
parameter receiver, generic free function) lower cleanly: the importer must
not own the generic class for the specialization id to escape its table.

## Workaround sites (all tagged `@workaround bug=rti004-mono-20261101`)

Every site binds the call to a local annotated with the callee's declared
return type and matches the local; the arms are unchanged, so behaviour is
identical.

- `src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl` (8 sites):
  `reserve_result: Result<RingReservation, SimpleRingError>` (reserve),
  `commit_result: Result<RingToken, SimpleRingError>` (commit),
  `delivered: Result<AsyncWakeCursorI64, SimpleRingError>` (`async_ref_deliver_wake_i64<i64>`),
  `released_completion` / `release_result` x2 / `cancelled: Result<(), SimpleRingError>`
  (release_retained_completion, release in `_release_reserved` and `_cancel_and_release`,
  complete_cancelled), `cancel_outcome: RingCancelOutcome` (cancel).
- `src/lib/nogc_async_mut/async_ring/async_ref.spl` (2 sites, `async_ref_deliver_wake_i64`):
  `completed` / `failed: Result<(), SimpleRingError>` (complete_success, complete_failure).
- `src/lib/nogc_async_mut/async_ring/simple_ring.spl` (1 site, `cancel`, Reserved arm):
  `release_result: Result<(), SimpleRingError> = self._release_slot(slot)`; the arms are
  additionally qualified `Result.Ok` / `Result.Err` as the diagnostic asks (plain
  hygiene, not load-bearing).

Regression spec: `test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_rti004_wa_spec.spl`
(behaviour of the rewritten `cancel` arms plus a source guard that no
`match self.ring.<call>(` / `match ring.<call>(` subject and no untyped
`release_result` binder returns). Not executed in this session: stage2 has no
`test` command and the Rust seed cannot parse the release stdlib
(`windows_tracked_seed_cannot_parse_release_stdlib_2026-10-10`).

## Evidence (pinned stage2, `compile --format=smf --source src/lib --source src/compiler --source src/app --keep-going --go-to-end`, entry importing the three modules, 77-module closure, 8 GB watchdog)

- before: `phase=mir state=failed ... done=77 total=77 succeeded=73 failed=4`; 44x
  `E-RTI-004` (ids 1125899906842624..635 across the 10 listed lines), 1x
  `RingCancelOutcome.CancelRejected: payload type mismatch` (`SimpleRing__cancel$i64_i64`),
  2x pre-existing `E-RTI-007 enum:Poll::unwrap` (`lib.nogc_async_mut.async.poll`,
  owned elsewhere); 71 s, peak RSS 0.95 GB.
- after: `phase=mir state=failed ... done=77 total=77 succeeded=76 failed=1`; 0x
  `E-RTI-004`, 0x simple_ring errors; the only failure is the out-of-scope poll
  module; 60 s, peak RSS 0.90 GB.

## Removal condition

Drop the typed binders once the bootstrap stage2 is rebuilt from a source that
either has no specialization pass (current `release/1.0.0`) or registers
specialization symbols in every importing module's table before MIR consults
RTI. The `Result.Ok` / `Result.Err` qualification in `simple_ring.spl` can stay.
