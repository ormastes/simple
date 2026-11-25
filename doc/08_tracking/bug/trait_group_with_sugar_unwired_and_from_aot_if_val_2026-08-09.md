# Trait-group `with` sugar is unreachable, and the generated `.from()` capability check is AOT-broken
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-08-09 (stream P0b, while correcting the unsound `.from()` shape)
**Related:** `capability_group_from_unsound_under_value_semantics_2026-08-09.md`
**Affects:** `src/app/desugar/trait_desugar.spl`,
`doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md` §3

Two blockers found while trying to complete P0's designated follow-up
(convert the hand-written `src/lib/common/debug/debug_profiler.spl` group to
the `with` sugar). Both were invisible to the existing tests because every
assertion about the group sugar checks EMITTED TEXT, never compiled output.

## 1. The `with` sugar is not wired into any compile path — BLOCKS the conversion

`desugar_traits` has **zero callers outside its own module**:

```
$ /usr/bin/grep -rn "desugar_traits" src/ --include=*.spl | grep -v app/desugar/
(no output)
```

It is a standalone source-text rewrite that nothing invokes.

> **CORRECTION 2026-08-09 (coordinator).** The transcript below is real, but its
> stated cause is wrong, and the fix it implies is already done.
>
> **The parser is NOT missing the production.** P0 landed the trait-header `with`
> clause in `50f06dcdd56`
> (`src/compiler_rust/parser/src/types_def/trait_impl_parsing.rs`), proven by
> `cargo test -p simple-parser` — which compiles the parser from source.
>
> The `bin/simple run` below failed because the **deployed seed binary is stale**:
> its mtime is `2026-08-09 04:50:31`, while P0 landed at `2026-08-09 11:43:04` —
> the binary predates the parser change by about seven hours. It is a
> stale-binary measurement artifact, not a grammar gap. Rebuilding the seed makes
> this transcript stop reproducing.
>
> Therefore strike the remedy "or the parser learns the trait-header `with`
> production directly" further down — that work is complete. The genuine
> remaining blockers are exactly two: **(a)** `desugar_traits` has no caller in
> any compile path (the finding above, which stands on its own evidence), and
> **(b)** the seed must be rebuilt for P0's parser change to reach any
> `bin/simple` invocation.
>
> This is the repo's standing binary-provenance trap: a `bin/simple` result is
> only evidence about the binary that produced it. Record binary identity
> alongside any claim that a language feature "does not work".

The stale-binary transcript, kept for the record:

```
$ cat tmp_tg.spl
trait A:
    fn a() -> i64

trait B:
    fn b() -> i64

trait AB with A, B:
    pass_dn

fn main():
    print "ok"

$ bin/simple run tmp_tg.spl
error: compile failed: parse: Unexpected token: expected Colon, found With
```

**Consequence:** `src/lib/common/debug/debug_profiler.spl` CANNOT be converted
from its hand-written form to `trait DebugProfiler with DebugTarget,
ProfileTarget:` — the file would stop compiling. The hand-written group stays
until the desugar pass is actually invoked by the driver (or the parser learns
the trait-header `with` production directly). This is not a sugar-expressiveness
gap: the emitted struct is field-for-field identical to the hand-written trait.
It is a wiring gap.

## 2. The generated `.from()` capability check is a NO-OP under native AOT

The generated body checks each member capability with `if val`. That idiom is
broken in the AOT lane — a real `nil` takes the `Some` branch:

```
$ cat tmp_ifval.spl
fn none_opt() -> Option<i64>:
    nil

fn main():
    val o = none_opt()
    if val x = o:
        print "SOME"
    else:
        print "NONE"

$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run tmp_ifval.spl
NONE
$ bin/simple native-build tmp_ifval.spl -o /tmp/tif && /tmp/tif
SOME
```

**Consequence:** compiled natively, `G__from()` would report every capability
present and hand back a group even when a member accessor returned `None` —
all-or-nothing acquisition silently fails OPEN. The regression spec
`test/01_unit/app/desugar/trait_group_from_execution_spec.spl` proves the
None path is correct on the interpreted lane only; it does not and cannot
cover AOT while the sugar is unreachable (blocker 1).

Fix order: blocker 2 must be closed (or `.from()` re-expressed with an
AOT-sound Option test) before the sugar is wired, or wiring it ships a
fail-open capability check.


## Triage 2026-11-25 (P2 fleet, release/1.0.0 @ d1b74b3fa1d) — both named blockers resolved; a third, seed-side defect is now the blocker

Measured on the tracked release/1.0.0 binary (`bin/simple.exe`, Rust seed
v1.0.0-rc.1) with scratch probes (not committed):

1. **Blocker 1 (sugar unwired / unparseable) — RESOLVED.** `trait AB with
   A, B:` parses and runs on the pinned binary (`fn main(): print "ok"` →
   `ok`). Independently, `desugar_traits` now has a real caller:
   `src/app/desugar/mod.spl:214` (`desugar_source` pipeline), reachable via
   the `bin/simple desugar` CLI command
   (`src/app/cli/_CliMain/main_and_help.spl:667-668`).
2. **Blocker 2 (`if val` fail-open in generated `.from()`) — RESOLVED in
   source.** `_gen_group_froms`
   (`src/app/desugar/trait_desugar.spl:119-206`) no longer emits `if val`;
   the capability check is a `match __oN: Some(_)/_` over each accessor
   result (AOT-sound Option test), followed by single-value acquisition —
   exactly the re-expression this entry demanded. (AOT execution could not be
   re-run here: `native-build` on the pinned binary aborts on the known
   `@representation_boundary` seed/source inconsistency, so this half is
   verified by code inspection.)
3. **New/remaining blocker — group dispatch is broken in the seed runtime.**
   A class implementing `A` and `B`, passed as `AB`, fails at runtime:
   `Runtime error: Function 'AB.a_id' not found` (reproduced 2026-11-25 on the
   pinned binary; same measurement recorded in
   `src/lib/common/debug/debug_profiler.spl` header and in
   `trait_group_with_sugar_status_f5_2026-08-09.md`). Until the seed's
   supertrait/group dispatch resolves member calls, `debug_profiler.spl`
   cannot be converted to the `with` form.

Classification: the remaining defect lives in the Rust seed
(`src/compiler_rust/**`); this lane may not rebuild the seed, so no source fix
is landed here. Left OPEN, re-scoped to the dispatch defect. Companion status
doc `trait_group_with_sugar_status_f5_2026-08-09.md` carries the same
2026-11-25 measurement.
