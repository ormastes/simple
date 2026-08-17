# Seed stage4 lane: optional-in-argument + mixed-tail miscompiles

> ## 2026-08-17 (worker W5): BLOCKED on verification lane; workarounds confirmed still load-bearing
>
> Both defects are properties of the Rust seed's `SIMPLE_BOOTSTRAP=1` stage4 NATIVE
> lane. Reproducing or ablating either requires a stage4 full-CLI build, which this
> session must not run, and the ordinary seed `run` path does not exercise that lane.
> No probe in this session can speak to it, so none is quoted.
>
> What IS verifiable here is that the mandatory workarounds are still in place and
> still commented as such -- e.g. `operand_type` in
> `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:1420` carries
> `val local_value = local ?? LocalId(id: -1)` with the note that "Stage4 `if val`
> can lose the LocalId payload", which is Defect 1's flat-optional shape, and
> `local_type` just above it records a removed `local.?` gate that "is FALSE on the
> stage4 lane and skipped EVERY local". So the lane's optional-handling hazard is
> still being routed around rather than fixed.
>
> Consequence worth stating plainly: these workarounds are load-bearing, so any
> future cleanup that "simplifies" them back to `if val` / `.?` will silently
> reintroduce Defect 1. Still OPEN.
>
> **FAMILY checked and REJECTED:** this row's Defect 1 (optional in argument
> position) was grouped with `pure_simple_text_extern_abi_audit_2026-07-30` as a
> possible shared argument-passing-ABI cause. They are NOT the same defect. This row
> is about an OPTIONAL argument's flat-nullable representation being lost on one
> backend lane; that row is about `text` being deliberately passed as ONE word
> instead of a `(ptr, len)` PAIR, i.e. an argument-count/convention mismatch that is
> uniform across all three pure-Simple backends by design. Different mechanism,
> different fix, correctly filed apart.


- **Date:** 2026-07-23
- **Component:** Rust seed `SIMPLE_BOOTSTRAP=1` native lane (stage4 full-CLI build)
- **Severity:** critical (silently wrong code in the self-hosted AOT driver)
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Defect 1 — optional in argument position never invokes the callee

Passing a flat optional (`LocalId?`), or a **field of a match-arm-bound flat
optional** (`local.id` where `case Copy(local)` bound `local: LocalId?`), as a
function argument is miscompiled:

- the callee **never executes** (an entry `print` in the callee does not fire), and
- the call appears to return garbage/0 (observed `untag(-1)` = `0x1FFFFFFFFFFFFFFF`,
  or plain 0 reused via one `xor r14,r14` for every later argument).

At the field-access variant the mechanism is not isolated between
non-invocation and the `if not opt.?` guard mis-branching to the early return;
both are cured by the same rewrite.

**Workaround (mandatory in stage4-lane code):** never factor optional-taking
helpers; extract inline at the use site:

```spl
var dest_id = -1
if val dest_id_l = dest:
    dest_id = dest_id_l.id
```

Proven in `cranelift_codegen_adapter.spl` (`cl_translate_operand` Copy/Move,
Call/CallIndirect dest handling, `operand_type`): side-by-side probe showed
inline extraction yields real ids while the helper call yields garbage; after
the rewrite VM-LOAD probe count went 2 → 60 and the compiled probe binary
produced its first correct output (`x5=42`).

## Defect 2 — mixed explicit/implicit return loses match-arm tail values

A function that contains any explicit `return` **and** relies on an implicit
match-arm/if tail value returns 0 through the implicit tail on the stage4
native lane. Pure-tail functions are fine.

**Workaround:** make every value tail an explicit `return`
(`cranelift_runtime_imports.spl`, `cl_translate_call`, `cl_translate_operand`,
`cl_translate_const_value`, `load_local`, `local_type`, `operand_type`).

## Related defect family (same lane, previously pinned)

- explicit `Some(...)` builds a heap enum box where a flat optional is expected
  (box header `0x100000004` read as payload) — bare-lift instead:
  `var d: T? = nil; if cond: d = value` (`mir_data.spl` emit_call/emit_call_indirect).
- `.unwrap()` lowers to box-assuming `rt_enum_payload` — breaks flat optionals.
- `Dict.get` returns tagged values / 0-nil on miss that if-val wrongly enters —
  use `has()` for the miss case + bracket-index or single `.get` + nil-check.

## Defect 3 — receiver-transport on call-return bindings (probe-masked)

A method called on a value bound from a method-call return
(`val bs = self.g.get_or_create_borrows(p); bs.active_borrows()`) reads `self`
fields as nil inside the callee — the nil-receiver guard fires (SIGILL via
`rt_eprintln_str` + `ud2`). **Entry `print` statements in the callee mask the
defect** (they force the receiver to materialize), so a build with debug
probes passes and the stripped build crashes — strip probes BEFORE the
conclusion-bearing verification build.

**Workaround:** free functions taking the underlying Dict handle as a plain
argument (`borrowset_active_list` / `borrowset_conflicting` in
`borrow_graph.spl`, used by `nll.spl` check paths).

## Pairing rule (sharpest form of the optional defect)

The defect is a PRODUCER/CONSUMER REPRESENTATION MISMATCH, not "Some is always
wrong": Some-box producer + `case Some(x)` consumer works (both boxed); flat
producer (bare-lift) + if-val consumer works; ANY mix breaks (if-val binds a
box un-unwrapped; `case Some`/`.unwrap()` on a flat value gives garbage or a
trap). Bare-lift a producer ONLY together with flipping every consumer of that
payload to if-val (grep for `case Some(`/`.unwrap()` on it first). Hit twice:
`end_function` (match-Some on freshly flattened `current_function`) and the
`HirStmtKind.Let` type payload (flat flip broke `mir_lowering_stmts` case-Some
consumers → universal SIGILL; producer flip reverted instead).

## Fixed alongside (real shared-MIR bugs found while peeling, not lane-specific)

- `lower_enum_match` dropped wildcard positions from the payload-bind list:
  `A(_,_,v)` bound v to the tuple BOX (bind-count-1 fast path misfire) and
  `A(_,t,v)` shifted every bind left (bind index used as tuple slot). Fixed
  with `enum_pat_binding_positions`/`enum_pat_arity` + declared-slot indexing
  + per-slot text retag via `enum_tuple_text_slots` (construction-site
  tracking in `box_tuple_payload`). Affected the LLVM lane too.
- `rt_enum_new` id/disc were emitted as I32 consts against the cranelift
  lane's uniform-i64 convention — every payload-enum construct failed
  cranelift verification. Emitted as I64 now (C ABI reads low 32 bits).
- `compile_module_with_backend` had no return-type annotation — the receiver
  was void-typed at method resolution and `.is_err()`/`.unwrap_err()`
  dispatched as `void.*` (masked every real backend error as an empty string).

## Separate defect (filed, not in this family): `void.unwrap_err`

Compiling an enum/Result probe (`probe_enum3.spl`) through the same stage4
`native-build --backend cranelift` path fails with
`Simple runtime error: function not found: void.unwrap_err` — a Result-typed
call is void-typed at method-resolution time. Distinct from the call-wiring
family above; not blocked on it.

## Repro

`bin/simple` stage4 binary (built via `stage4_fixed_seed_build.sh`) compiling
`probe_trivJ.spl` (`val w5 = 4; val x5 = w5 * 10 + 2; print "x5={x5}"`) with
`native-build --backend cranelift`: before the workarounds the produced binary
was silent (rt_print rdi=0); after, it prints `x5=42`.

Note: `native_cache` does not reliably invalidate on source edit — `rm -rf`
the cache dir before any conclusion-bearing rebuild.
