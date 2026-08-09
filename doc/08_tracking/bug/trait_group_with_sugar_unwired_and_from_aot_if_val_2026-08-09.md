# Trait-group `with` sugar is unreachable, and the generated `.from()` capability check is AOT-broken

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

It is a standalone source-text rewrite that nothing invokes. The parser
therefore never sees the desugared form, and rejects the sugar outright:

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
