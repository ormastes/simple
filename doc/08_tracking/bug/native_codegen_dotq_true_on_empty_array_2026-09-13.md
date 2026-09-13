# `.?` on an empty array evaluates TRUE under native codegen

- Status: OPEN (2026-09-13) — the compiler defect is NOT fixed. One caller
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
