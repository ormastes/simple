# BUG: `class` instances copy on binding, and `for` loop mutation is discarded entirely

## Re-measured 2026-09-13 — still OPEN. Now a clean LANE DIVERGENCE, and the affected-spec list is re-triaged

Binary: Rust seed `build/vt4/bootstrap/simple.exe` (sha256 `dc138d50276d…`),
Windows.

### The language behaviour: JIT is correct, the interpreter is not

The entry's own `probe_ref2.spl`, run verbatim inside `fn main()`:

| checkpoint | what it tests | **JIT (default)** | **`SIMPLE_EXECUTION_MODE=interpret`** | contract |
|---|---|---|---|---|
| `P_before` | baseline | `xs0=0 c1=0` | `xs0=0 c1=0` | — |
| `Q_after_loop` | `for c in xs: c.bump()` | `xs0=1 c1=1` ✓ | **`xs0=0 c1=0`** ✗ | 1 / 1 |
| `R_after_index` | `xs[0].bump()` | `xs0=2 c1=2` ✓ | **`xs0=1 c1=0`** ✗ | 2 / 2 |
| `S_alias` | `val a = c1; a.bump()` | `c1=3 a=3` ✓ | **`c1=0 a=1`** ✗ | 3 / 3 |

The default JIT lane now honours `doc/07_guide/language/syntax.md:460`'s
`class Person:  # Reference type` on all three checkpoints. The tree-walking
interpreter still implements full value semantics and fails all three,
including the headline `for`-loop symptom, with exit 0 and no diagnostic.

So this is no longer "the language behaves as a value type" — it is a two-lane
divergence with a known-good side, which gives any fix a reference
implementation to match and a ready differential oracle.

### The affected specs: re-run, and MOST of the 11 failures were something else

**The spec harness runs the interpreter lane** — the bad one. Verified in-run
with a `print "{not nil}"` probe inside an `it` (harness prints `true`; the JIT
prints `false`). So these specs do exercise the defect.

Re-ran all five named specs:

| spec | before this pass | cause of remaining failures |
|---|---|---|
| `mock_spec.spl` | 4 total, **0 failed** | — |
| `mock_phase3_spec.spl` | 31 total, **0 failed** | — |
| `mock_phase4_spec.spl` | 24 total, **0 failed** | — |
| `mock_phase5_spec.spl` | 28 total, 6 failed | **not this bug** — 6 × `semantic: unknown static method create on class MockFunction`; the class declares `static fn new`, never `create` (`src/lib/common/testing/mock/builder.spl:45`). A plain wrong method name in the spec. **Fixed in this pass** (`MockFunction.create(` -> `MockFunction.new(`, both the `test/01_unit/std/` and legacy `test/unit/std/` copies): now **28 total, 27 passed, 1 failed**. The pair was already divergent and stays divergent, so the test-tree divergence baseline is unaffected. |
| `mock_phase6_spec.spl` | 59 total, 4 failed | consistent with this bug — `gets total calls across mocks` expected 3 got **0**, `gets total delay across mocks` expected 120 got **0**, `orchestrates multiple async services` expected 160 got **0**, `verifies all mocks called` got false: mutations to registered mocks are invisible through the registry. |

That leaves at most **5** failures attributable to this defect, not 11 — **1
verified plus 4 consistent-but-unverified**:

- **Verified (1).** phase5's single survivor, `chains when with returns`.
  `FluentExpectation.create(mockfn)` then
  `fluent.when_called_with(["data"]).returns("result")` leaves
  `mockfn.return_values.len()` at 0. The callee was checked rather than
  assumed: `FluentExpectation` (`src/lib/nogc_async_mut/src/testing/mock/verification.spl:326`)
  holds `mockfn: MockFunction` as a field, and `me returns(value)` at `:337`
  really does call `self.mockfn.set_return_values([value])` on both its match
  arms. So under reference semantics the caller's `mockfn` would see the write,
  and under the interpreter's value semantics it does not — this is exactly the
  `S_alias` checkpoint above, one object deep. It is a clean, small,
  harness-runnable regression probe for this bug.
- **Consistent but unverified (4).** phase6's four. Their shape — mutations to
  registered mocks invisible through a registry, every aggregate reading 0 —
  matches this defect, but no callee was inspected and no alternative cause was
  ruled out. Do not count them as proven without doing for them what was done
  for the phase5 survivor.

### Severity

Still high for the interpreter lane and therefore for the whole spec harness,
but no longer a silent wrong answer on the default `simple run` path.

Not fixed here — the interpreter is `src/compiler_rust/**`, off-limits during
this pass (concurrent bootstrap).
**Status:** OPEN
**Found:** 2026-08-04
**Severity:** high — `doc/07_guide/language/syntax.md:460` documents `class` as a
**reference type**; it behaves as a value type. Mutation through a `for` loop
variable is lost silently, with no diagnostic and exit 0.
**Files:**
- documented contract: `doc/07_guide/language/syntax.md:460` (`class Person:  # Reference type`)
- affected specs: `test/01_unit/std/mock_phase3_spec.spl`,
  `mock_phase4_spec.spl`, `mock_phase5_spec.spl`, `mock_phase6_spec.spl`,
  `mock_spec.spl` (11 failing examples), plus the legacy duplicates under
  `test/unit/std/`

## Symptom

`/tmp/probe_ref2.spl`, run with `SIMPLE_EXECUTION_MODE=interpreter`:

```
class Counter:
    n: i64
    static fn new() -> Counter:
        Counter(n: 0)
    me bump():
        self.n = self.n + 1

fn main():
    val c1 = Counter.new()
    val c2 = Counter.new()
    val xs = [c1, c2]
    print "P_before xs0={xs[0].n} c1={c1.n}"
    for c in xs:
        c.bump()
    print "Q_after_loop xs0={xs[0].n} c1={c1.n}"
    xs[0].bump()
    print "R_after_index xs0={xs[0].n} c1={c1.n}"
    val a = c1
    a.bump()
    print "S_alias c1={c1.n} a={a.n}"
```

| line | actual | expected for a reference type |
|------|--------|-------------------------------|
| `P_before` | `xs0=0 c1=0` | `xs0=0 c1=0` ✅ |
| `Q_after_loop` | **`xs0=0 c1=0`** | `xs0=1 c1=1` |
| `R_after_index` | `xs0=1 c1=0` | `xs0=2 c1=2` |
| `S_alias` | **`c1=0 a=1`** | `c1=1 a=1` |

Two separate breakages:

- **`Q`** — `for c in xs: c.bump()` changed **nothing at all**. Not the aliased
  `c1`, and not even `xs[0]` itself. The loop variable is a copy and the copy is
  thrown away at the end of each iteration. Compare `R`, where `xs[0].bump()`
  through an index *does* land on the element.
- **`S`** — `val a = c1` copies. Mutating `a` leaves `c1` untouched. Plain
  binding of a class instance does not alias.

## Root cause

`class` is being given struct/value copy semantics on binding and on
`for`-iteration. What is **proved** here is the observable behaviour above plus
the documented contract it violates (`syntax.md:460`); the exact copy site in
the interpreter is not yet pinned to a file:line, and pinning it is the first
step of the fix rather than something to assume.

Note `R` vs `Q`: index assignment reaches the element while the loop variable
does not, so the two paths do not share a lowering. Any fix must cover both.

## How it reaches the suite

`test/01_unit/std/mock_phase4_spec.spl:290` defines a local
`class MockComposition: mocks: [MockFunction]` whose `reset_all` is

```
me reset_all():
    for mockfn in self.mocks:
        mockfn.reset()
```

which is exactly case **Q** — it resets nothing:

```
✗ resets all mocks in composition       expected 2 to equal 0
```

and its `add_mock` stores a copy, which is case **S** — calls recorded on a mock
*after* it is added never reach the composition:

```
✗ uses state machine with mock composition   expected 0 to equal 2
✗ manages complex multi-mock workflow        expected 0 to equal 3
✗ gets total calls across mocks              expected 0 to equal 3     (mock_phase6)
✗ gets total delay across mocks              expected 0 to equal 120   (mock_phase6)
✗ orchestrates multiple async services       expected 0 to equal 160   (mock_phase6)
```

Note also `add_mock`'s body:

```
me add_mock(mockfn: MockFunction):
    var mocks = self.mocks
    mocks.append(mockfn)
    self.mocks = mocks
```

— the read-modify-write-back dance is a workaround already forced by array value
semantics, so the spec author had hit an adjacent version of this.

## Why not fixed now

Changing `class` binding and `for`-iteration to reference semantics is a
core object-model change in the interpreter and in MIR lowering. It alters the
meaning of every `class` in the repo, including places that may now silently
depend on the copy (the `var xs = self.items; ...; self.items = xs` pattern above
is written *because* of value semantics and would keep working, but code that
relies on a defensive copy would change behaviour). It needs its own lane with a
full-suite before/after, not a drive-by fix from a test-repair pass.

The two halves can land independently, and the `for`-loop half (**Q**) is both
the smaller change and the more clearly-wrong behaviour — it discards a write
that the equivalent indexed write (**R**) performs.

**Do not "fix" the mock specs by rewriting them to avoid `for`.** The specs are
correct against the documented reference-type contract; the runtime is not.

## Related

- `doc/08_tracking/bug/vulkan_bind_pipeline_refused_after_readback_2026-09-11.md`
  (R1) — a likely instance of this same class-instance copy-on-bind defect,
  observed in the Engine2D Vulkan backend: a mutation of `VulkanBackend`'s
  pending-compute state was dropped instead of written back, reviving a freed
  command-buffer handle across frames. R1's guard
  (`vulkan_discard_stale_pending_compute()`) covers only the pending-compute
  fields it explicitly resets — it is a targeted workaround for one field, not
  a fix for the underlying copy-on-bind/for-loop mutation-drop defect
  documented here.
