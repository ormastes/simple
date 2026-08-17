# BUG: `class` instances copy on binding, and `for` loop mutation is discarded entirely

**Status:** RESOLVED — ALREADY-FIXED, re-verified 2026-08-17.

## Re-verification 2026-08-17 (partial-fix sweep, lane 1)

Both halves of the filing re-probed verbatim on the deployed seed
(`bin/simple`, Rust seed dated 2026-08-16):

```
for c in xs: c.bump()   ->  xs[0].n == 1   (was: mutation dropped)
val a = c1; a.bump()    ->  c1.n  == 1     (was: copy-on-bind)

Results: 2 total, 2 passed, 0 failed
```

Class instances behave as reference types on this lane; neither the
copy-on-bind nor the for-loop-drops-mutation symptom occurs.

NOT PROVED: which commit fixed it (not bisected); the pure-Simple self-hosted
lane and the native/JIT lane were not probed.

--- original filing below, kept for history ---

**Status (original):** OPEN
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
