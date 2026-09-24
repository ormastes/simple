# `.?` on an empty array evaluates TRUE under native codegen

- Status: FIXED 2026-09-13 (see the FIXED section at the end of this file). Original triage below. One caller
  (`BuildGraph.topological_order`) has been routed around it; every other
  `x.?` on an array in natively-compiled code is still exposed.
- Severity: **silent wrong control flow.** No diagnostic, no crash. A `while
  arr.?:` loop over an array that drains to empty never terminates; an `if
  arr.?:` takes the wrong branch. This was the root cause of site 9, the
  `--stop-after-stage2` blocker on BOTH the macOS and the Linux bootstrap lane
  (`stage2_stage3_route_native_compile_timeout_2026-09-13.md`).
- Measured on: `aarch64-apple-darwin`, `--backend llvm`, `--mode dynload`,
  compiler = run-21 Stage-2 runtime authority
  (`.../bootstrap-run21/stage3/aarch64-apple-darwin/stage2-runtime-authority/simple`).
  The Linux lane shows the same site-9 signature and the same seed, so it is
  very likely not darwin-specific — **that has not been measured here** and
  should not be asserted without a Linux fixture run.

## Reproduction — 10 lines, 2.2 s to compile

```
fn main():
    var a: [i64] = []
    var n = 0
    while a.?:
        n = n + 1
        if n > 5:
            break
    print "never-popped empty [i64], while a.?: iterations (cap 5) = {n}, len={a.len()}"
    var e: [(i64, bool)] = []
    var m = 0
    while e.?:
        m = m + 1
        if m > 5:
            break
    print "never-popped empty [(i64,bool)], while e.?: iterations (cap 5) = {m}, len={e.len()}"
    var f = [7]
    var k = 0
    while f.?:
        f.pop()
        k = k + 1
        if k > 5:
            break
    print "one-elem [i64] drained by pop, iterations (cap 5) = {k}, len={f.len()}"
    if a.?:
        print "if a.?: TAKEN (wrong)"
    else:
        print "if a.?: not taken (correct)"
```

Built with `native-build --target aarch64-apple-darwin --backend llvm
--runtime-bundle core-c-bootstrap --threads 1 --mode dynload`, then run:

```
never-popped empty [i64], while a.?: iterations (cap 5) = 6, len=0
never-popped empty [(i64,bool)], while e.?: iterations (cap 5) = 6, len=0
one-elem [i64] drained by pop, iterations (cap 5) = 6, len=0
if a.?: TAKEN (wrong)
```

Every loop hit its cap. Every array reports `len()==0` in the same binary at the
same point. So:

- **`.len()` is correct; `.?` is not.** They disagree inside one native build.
- It is **not** a post-`pop()` length/capacity split — a never-popped empty
  literal fails identically. It is `.?` on an empty array, unconditionally.
- It is **not** specific to the loop form — the plain `if a.?:` takes the wrong
  branch too, so it is the truthiness test itself, not a hoisted loop condition.
- Element type is irrelevant (`[i64]` and `[(i64, bool)]` both fail).

A second, smaller divergence was seen while probing and is recorded but not
chased: `{a.?}` in an interpolation prints `[]` (the array) rather than a bool,
so `.?` does not appear to be producing a boolean value in value position either.

## How it presented (site 9)

`BuildGraph.topological_order` (`src/compiler/80.driver/driver_build/parallel.spl`)
walks a DFS with `while stack.?:` / `stack.pop().unwrap()`. Instrumented output
from a Stage-2 candidate, on the real 2-unit graph the Stage-3 route builds:

```
[TOPO-PROBE] units.keys().len()=2
[TOPO-PROBE] unit id=0 deps.len()=0
[TOPO-PROBE] unit id=1 deps.len()=0
[TOPO-PROBE] iter=1 stack.len()=1 order.len()=0
[TOPO-PROBE]   popped node=0 expanded=false stack_after_pop=0 visited_has_node=false
[TOPO-PROBE] iter=2 stack.len()=1 order.len()=0
[TOPO-PROBE]   popped node=0 expanded=true stack_after_pop=0 visited_has_node=true
[TOPO-PROBE] iter=3 stack.len()=0 order.len()=1        <- stack is EMPTY
[TOPO-PROBE]   popped node=nil expanded=nil ...        <- loop entered anyway
[TOPO-PROBE] iter=4 stack.len()=1 order.len()=1
[TOPO-PROBE]   popped node=nil expanded=true ...
[TOPO-PROBE] iter=5 stack.len()=0 order.len()=2
...
```

`iter=3` is the defect in one line: `stack.len()` is 0 and the `while stack.?:`
body ran. From there the loop is a stable 2-cycle — pop nil, `visited[nil]=true`,
push `(nil, true)`, pop it, `order.push(nil)` — appending one nil to `order`
every two iterations, forever.

Three secondary divergences are visible in that trace. None is load-bearing (the
`.?` defect alone is sufficient) but each is real and each made the failure
quieter than it should have been:

1. `stack.pop()` on an empty array yields something whose `.unwrap()` succeeds
   and produces `nil`, rather than `None`/a failure.
2. `visited[nil] = true` does not make `visited.has(nil)` true on the next
   iteration — so the visited guard could not break the cycle.
3. Because (2) fails, `order` grows without bound. **That is the Linux lane's
   monotonic ~1.9 GB/45 s RSS growth**, which the site-9 record had listed as an
   unexplained difference from the macOS flat/falling curve. Same defect; the
   macOS curve is an allocator artifact, not a different failure.

## Fix status and blast radius

Not fixed. `BuildGraph.topological_order` now guards with `stack.len() > 0` and
carries a comment pointing here; that comment and this record are what license
the deviation from house style (`.?` is preferred), per CLAUDE.md's rule against
silently normalizing a workaround for a failing compact form.

**Every other `x.?` on an array in code that is natively compiled is still
exposed** — including any that runs in the bootstrap closure. A census of
`while <ident>.?:` / `if <ident>.?:` sites where the receiver is an array is the
natural follow-up and has not been done. The correct repair is in the codegen
that lowers `.?` for array receivers, not in the call sites.

## Adjacent finding, met while writing the spec (separate defect, OPEN)

`test/01_unit/compiler/driver/build_graph_topological_order_terminates_spec.spl`
could not assert unit identity the obvious way. Inside a spec `it` closure, an
`i64` taken out of the returned `order` does not compare equal to the `i64` that
`add_unit` returned for the same unit, on the **seed interpreter**:

```
DBG a=0 b=1 order.len()=2
DBG entry=0
DBG entry=1
DBG has_a=false has_b=false      <- order holds 0 and 1, a == 0
```

`order.contains(a)` answers false, and a bare `id == a` in a position scan is
likewise false, so every position stayed `-1`. The identical code in a plain
`fn main()` script (same binary, same module) prints `contains(a)=true`. So it is
specific to values crossing the spec closure boundary, not to `contains`.

This is the same family as the documented "chained methods on erased receivers"
limitation. It is NOT the `.?` defect above (that one is native-codegen-only;
this one is the interpreter), and it is not fixed. The spec renders both sides to
text to pin the ordering contract instead, with a comment saying why — the
workaround is recorded here rather than silently normalized.

## FIXED 2026-09-13 — `.?` now means presence, not "not the nil sentinel"

Status above (OPEN) is superseded for the compiler defect itself. The
call-site workaround in `BuildGraph.topological_order` is left in place and is
now redundant, not load-bearing.

### Root cause, one line

`.?` (`Expr::ExistsCheck`) lowered to the runtime predicate **`rt_is_some`**,
which is pure nil/None presence — an empty-but-allocated array is `Some`.
`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2084` (condition
position, `lower_condition`), `:2238` (`coerce_exists_value_to_bool_in_place`,
the `-> bool` tail form) and `:2365` (`lower_exists_check`, value position) all
named it. The backends were innocent: there is no `.?`-specific emitter — both
LLVM and Cranelift just emit a MIR `Call` to whatever symbol the HIR names, so
both were wrong identically. `.len()` stayed right because it never routed
through that predicate.

The interpreter never agreed: `compiler/src/interpreter/expr.rs:533-567`
decides presence itself and returns `Value::Nil` when absent, and
`interpreter_control.rs:172-188` (`is_condition_present`) branches on "not
`Value::Nil`". The tree-walk rule, verbatim, after unwrapping any
Option/Result layer:

| receiver | `.?` |
|---|---|
| nil / `None` / `Err` | absent |
| empty array, empty dict, empty string | **absent** |
| `Set` with empty `items` | absent |
| everything else — `0`, `false`, `0.0`, tuples, closures, structs | present |

That last row is deliberate and must not be "simplified" into generic
truthiness: doing so is the "0 is falsy" landmine
(`seed_interp_option_match_falls_through_at_scale_2026-07-18.md`).

### The fix

A new runtime predicate `rt_is_present` implements exactly the table above, in
all three runtimes that must stay twins:

- `src/compiler_rust/runtime/src/value/objects.rs` (Rust runtime)
- `src/runtime/runtime_native.c` + declaration in `src/runtime/runtime.h` (C)
- `src/runtime/simple_core/core_string.spl` (pure-Simple core archive)

and the three `.?` lowering sites now name it. `rt_is_some` is untouched and
still backs the raw optional/pointer-slot probes at `control.rs:669` and
`:2162`, which really do mean "not the nil sentinel".

### Evidence — `test/04_smoke/dotq_empty_collection_presence_probe.spl`

Five shapes (F61's four plus a non-empty control), self-checking, `PASS`/`FAIL`
per line. Built by the seed's native pipeline,
`native-build --target aarch64-apple-darwin --backend cranelift
--runtime-bundle core-c-bootstrap --threads 1 --mode dynload`, same seed binary
before and after the lowering change:

```
before (rt_is_some)                          after (rt_is_present)
FAIL empty [i64] while a.?: 6 iterations     PASS empty [i64] while a.?: 0 iterations
FAIL empty [(i64,bool)] while e.?: 6 iter    PASS empty [(i64,bool)] while e.?: 0 iterations
FAIL one-elem drained by pop: 6 iterations   PASS one-elem [i64] drained by pop: 1 iteration
FAIL if a.?: TAKEN on empty array            PASS if a.?: not taken on empty array
PASS if g.?: taken on non-empty array        PASS if g.?: taken on non-empty array
probe failures = 4                           probe failures = 0
```

The same file under the interpreter (`simple run`) prints the same five
`PASS` lines — the engines now agree, which is the actual contract.

**No LLVM-side unit test exists.** `codegen/llvm/**` is feature-gated and this
host's seed has no `llvm` feature, so one could not be run here; the three tests
below cover the runtime table, the Cranelift type stamping, and the shared
declaration root, and that is the honest extent of it.

**Backend coverage, stated honestly.** The measured native run is
**Cranelift**; this host's seed is built without the `llvm` cargo feature
(`error: native backend 'llvm' is not available in this build`), so the LLVM
lane was not executed here. It is covered by construction rather than by
measurement: there is no `.?`-specific emitter on either side, the symbol is
declared once for both in `codegen/runtime_sffi.rs` and rooted once in
`codegen/common_backend.rs`, and the LLVM arity/returns-bool tables in
`codegen/llvm/functions/calls.rs` were updated in the same shape as
`rt_is_some`. A run on an LLVM-featured build is still worth doing.

Rust tests (sabotage → red → green verified on the first):

- `runtime/src/value/object_tests.rs::dotq_presence_matches_interpreter_exists_check_rule (deliberately NOT named `rt_*`: the rt-dual-implementation ratchet reads `fn rt_*` as a runtime symbol and flags a test helper as a new single-lane symbol)`
  — the full table, both directions, including the explicit assertion that
  `rt_is_some` is the WRONG predicate for an empty array.
- `codegen/instr/body.rs::build_vreg_types_stamps_rt_is_present_call_bool`
  — Cranelift stamps the presence call BOOL (else the branch tests a raw
  tagged word).
- `codegen/common_backend.rs::option_presence_predicate_runtime_symbols_are_retained`
  — `rt_is_present` is a codegen root, so neither lane leaves it undeclared.
  Without it the link fails closed, which is what it did on the first attempt:
  `1 runtime symbol(s) referenced by generated code have no definition ...
  _rt_is_present`.

### Census — where `.?` is used on a non-Optional receiver (for F62)

`grep -rnE '(while|if) +<ident>\.\?:' src/compiler src/lib` → **24** sites,
whose receivers read as Optionals **by variable name** (`op`, `ms`, `wc`, `id`,
`os`, `ew`, `em`, `re`, `al`, `el`) — classified by name, not by chasing each
declaration, so treat it as a strong indication rather than a proof. For an
Optional with a non-empty (or non-collection) payload the two predicates agree,
so those sites behaved the same before and after. Two were spot-checked against
their declarations: `shb_hash.spl:90`'s `re` is a struct optional (unaffected),
while `database/core.spl:320`'s `id` is a `text?` (`id ?? ""` on the next line)
— so a row whose primary key is the EMPTY STRING is no longer indexed on the
native lane. That is a real behavioural change and it is the intended one: the
interpreter has always skipped it. They are **not** unconditionally
unchanged: an `Optional<text>` holding `Some("")`, or an optional array holding
`Some([])`, now reports absent where it used to report present — which is the
correction, since that is what the interpreter has always answered.

The array-receiver population is the `while` forms, which that regex misses
when the condition is compound. Complete list — every one of these was silently
non-terminating under native codegen and is correct now:

- `src/compiler/90.tools/context_pack.spl:58` — `while to_process.?:`
- `src/compiler/10.frontend/parser/test_analyzer.spl:170` — `while indent_stack.? and ...`
- `src/compiler/10.frontend/parser/test_analyzer.spl:233` — `while group_stack.?:`
- `src/compiler/80.driver/driver_build/parallel.spl:274-305` — the site-9
  `topological_order` DFS, already routed around by hand; the `.len() > 0`
  guard there can now go back to `.?` at leisure.

The two `test_analyzer.spl` sites are in the **parser**, i.e. inside the
bootstrap closure — they were exposed on exactly the lane F62 is running.
The three `while current.?:` sites in `src/lib/*/gc.spl` walk an Optional node
cursor, not an array, and were unaffected.

### Related records — read before flipping this back

`existence_check_conflates_absent_with_empty_text_2026-08-10.md` argues the
OPPOSITE direction (absent should not be conflated with empty text). This change
pins `"".?` as **absent** on the native lane. That is not a re-litigation of that
record: the rule here is "match the interpreter", and the interpreter has decided
empty-string-is-absent since long before either record. If the language decides
the other way, the change belongs in `interpreter/expr.rs` FIRST and in
`rt_is_present` second — never in one engine alone, which is the whole defect
this file is about. See also
`dotq_presence_operator_is_bare_unwrap_outside_argument_position_2026-09-12.md`
and `dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27.md`.

### Not fixed here (separate, still OPEN)

`Err(x).?` is still **present** natively while the interpreter says absent:
`rt_is_present` unwraps via `rt_unwrap_or_self`, which only unwraps
`OPTION_ENUM_ID`, so a `Result` never reaches the emptiness check. Pre-existing
under `rt_is_some` too — not introduced here, not fixed here.

Also: the three secondary divergences in the site-9 trace — `pop()` on an empty array
unwrapping to `nil`, `visited[nil] = true` not making `has(nil)` true, and the
value-position `{a.?}` interpolation shape (see
`dotq_presence_operator_is_bare_unwrap_outside_argument_position_2026-09-12.md`,
which is the same family and remains open). `.?` in value position does now
yield nil for an empty collection, but the bare-unwrap-outside-argument-position
defect that record describes is untouched.
