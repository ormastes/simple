# BUG: `class` instances copy on binding, and `for` loop mutation is discarded entirely

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

## Additional observation 2026-09-06 — a class-typed FIELD is copied too

Same root defect, a third surface: storing a class instance into another
class's field copies it, so mutation through the holder never reaches the
original. Function-argument passing DOES alias correctly, which is what makes
this one easy to miss.

`repro_alias.spl` (macOS aarch64, `src/compiler_rust/target/debug/simple`,
interpreter path):

```
class Box:
    n: i64
impl Box:
    me bump():
        self.n = self.n + 1

class Holder:
    b: Box
impl Holder:
    static fn create(b: Box) -> Holder:
        Holder(b: b)
    me bump():
        self.b.bump()

fn bump_arg(b: Box):
    b.bump()

fn main():
    val x = Box(n: 0)
    bump_arg(x)
    print "after fn arg bump: {x.n} (expect 1)"      # -> 1   OK, aliased
    val h = Holder(b: x)
    h.bump()
    print "after holder field bump: {x.n} (expect 2)" # -> 1   WRONG, copied
    val h2 = Holder.create(x)
    h2.bump()
    print "after static-ctor bump: {x.n} (expect 3)"  # -> 1   WRONG, copied
```

**Field impact.** `parent_commit_piped_process_session_v1(cmd, args, gen, inbox)`
stores the caller's `ParentCommitFrameInboxV1` in
`ParentCommitPipedResultReaderV1.inbox`. After a successful poll the reader's
copy holds the accepted frame (`accepted_frames=1, frames_len=1`) while the
caller's inbox is still empty (`accepted_frames=0`), so `inbox.receive()`
returns `ok=false` and the commit reports `empty-process-result-batch`. This
blocks the first example of
`test/03_system/plan_acceptance/parent_authoritative_actor_process_spec.spl`.
Not worked around in library code deliberately: a registry or length-1-array
field would be implementing around a broken language primitive inside the
stdlib.
