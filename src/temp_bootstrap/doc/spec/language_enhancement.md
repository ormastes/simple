Below are two “drop-in” spec sections you can add to Simple’s language documentation. They are written as missing-feature documentation (what other languages formalize, what Simple should formalize), and then a proposed Simple specification (minimal but complete enough to implement).

I am basing the “what’s missing” on the fact that Simple’s README shows enums + match, plus GC/runtime concepts, but does not expose a formal aliasing model, concurrency memory model, or full match semantics/exhaustiveness rules in the publicly visible material.


---

5. Memory, Aliasing, and Concurrency Model

5.1 What’s typically present in other languages (and likely missing in Simple today)

A. Explicit aliasing rules for mutation

Modern languages either:

Enforce “no mutable aliasing” for safe references (Rust-style borrowing), i.e., you may have many readers or one writer, not both 

Or permit aliasing but require disciplined synchronization, with a formally defined memory model (Go/Java/C++).


If Simple has class references + mutation + concurrency, you need a formal answer to:

When can two references point to the same object?

What operations require exclusivity?

What is considered a data race?


B. A concurrency memory model (“happens-before”)

Languages with concurrency typically define visibility rules using happens-before and data race terminology. Go’s memory model is a well-known example, including the “data-race-free implies sequentially consistent behavior” guidance. 
Also, Go defines synchronization edges like “send on channel happens-before receive completes.” 

C. Atomic and synchronization primitives as language concepts

Without atomics/sync as first-class, you cannot precisely define:

what is guaranteed to be visible across threads/actors,

what reorderings are permitted,

which programs are “well-defined.”


5.2 Proposed Simple model: “Capabilities + DRF memory model” (minimal, implementable)

This is a pragmatic hybrid:

A capability discipline for mutation (compile-time restriction where possible),

A data-race-free (DRF) memory model for concurrency semantics, similar in spirit to Go’s guidance. 


5.2.1 Reference and capability kinds

Simple values fall into two broad categories (already implied by struct vs class):

struct: value semantics

class: reference semantics (GC-managed object identity)


For class references, define capabilities:

T : shared (read-only) reference

mut T : unique mutable capability

iso T : isolated (unique + transferable across concurrency boundaries)


Core rule (no mutable aliasing): At any point in time, for a given object:

either there are one or more T (shared read-only references),

or exactly one mut T (exclusive writer),

or exactly one iso T (exclusive + transferable), but not a mixture.


This captures the essential safety property commonly summarized as “mutable references allow mutation but prevent aliasing.” 

5.2.2 Conversions and borrowing

Allowed conversions (compile-time checked):

mut T -> T (downgrade to read-only view)

iso T -> mut T (consume isolation for local mutation)

iso T may be moved (transferred) into another actor/thread; mut T may not.


Disallowed:

T -> mut T unless you can prove uniqueness (typically not possible without ownership tracking).


5.2.3 Escapes and closures

If a closure captures a mut T, the compiler treats the capability as moved into the closure (it cannot be used elsewhere until the closure is dropped/exits), unless the closure is proven non-escaping.

This prevents accidental creation of two writers via capture.

5.2.4 Interior mutability (explicitly marked “unsafe-by-default”)

If you need mutation behind a shared reference, require explicit wrappers:

Atomic[T]

Mutex[T]

RwLock[T]


These wrappers define synchronization semantics (see §5.2.6).

5.2.5 Definition: data race (normative)

A data race occurs when two concurrent executions access the same memory location, at least one access is a write, and the accesses are not ordered by happens-before (or not done through atomics/locks). This is consistent with standard definitions used in Go-style models. 

5.2.6 Memory model: happens-before + DRF guarantee

Define a partial order happens-before. Key edges:

1. Program order within a single thread/actor: earlier statements happen-before later ones.


2. Synchronization edges:

Lock release happens-before subsequent lock acquire on the same mutex.

Atomic operations with appropriate ordering create happens-before edges (if you support ordering levels).

Message passing: send happens-before receive completion (if your actor/channel semantics match this model). 




DRF guarantee: If a Simple program has no data races, its executions behave as if operations were interleaved in a single global order consistent with happens-before (the “as-if sequential” intuition). This mirrors the practical contract used in Go’s memory model. 

5.2.7 What becomes “undefined / trap” vs “runtime error”

Decide one:

Option A (strict): data races are undefined behavior (max optimization freedom).

Option B (debuggable): data races are runtime traps in --san / test builds; unspecified otherwise.


(Go strongly encourages avoiding races and offers tooling support; you can follow that ergonomically.) 

5.2.8 Example (capabilities)

fn bump(x: mut Counter) -> i64:
    x.value += 1
    return x.value

fn read_only(x: Counter) -> i64:
    return x.value

fn demo(c: iso Counter):
    let m: mut Counter = c  # consume iso -> mut
    bump(m)
    let r: Counter = m      # mut -> shared view
    read_only(r)


---

7. Pattern Matching: Completeness, Exhaustiveness, and Guards

7.1 What’s typically present in other languages (and likely missing in Simple today)

If Simple already supports match on enums (as shown), the next “production-grade” features most languages add are:

1. Exhaustiveness checking: compiler proves match handles all cases (or forces a default). Rust explicitly checks match arms are exhaustive. 


2. Unreachable arm detection: warn/error if an arm can never match.


3. Guards: case P if cond to refine patterns without exploding cases.


4. Nested destructuring: tuples/struct/enum payload patterns with bindings.


5. Or-patterns: case A | B


6. Refutable vs irrefutable patterns: some patterns always match (usable in let), others only sometimes (usable in match/if let). Rust makes this distinction and documents pattern forms broadly. 



7.2 Proposed Simple match specification

7.2.1 Syntax

Assuming Simple is indentation-based:

match expr:
    case Pattern [if GuardExpr]:
        Block
    case Pattern:
        Block
    else:
        Block

else is optional only if the match is exhaustive.


7.2.2 Pattern forms (minimum set)

Borrowing the mainstream set of pattern constructs (Rust is a good reference for breadth). 

Literals

0, "x", true


Wildcard

_ matches anything, binds nothing


Binding

name binds the matched value to name

name: Type optional (if you want typed binds)


Enum case

Case

Case(p1, p2, ...) for payload/associated fields


Tuple

(p1, p2, ...)


Struct

Point{x: px, y: py}

Point{ x, y } shorthand binds x, y

Point{ x: 0, y: _ }


Or-pattern

P1 | P2 | P3


Range (optional)

1..=10 (integers/chars)


7.2.3 Guards

A guard is a boolean expression evaluated only after the pattern matches:

case Some(x) if x > 0:
    ...

Guards participate in exhaustiveness conservatively:

A guarded arm does not “cover” the full pattern space unless proven (generally assume it does not).


7.2.4 Evaluation order

match expr evaluates expr exactly once.

Arms are tested top-to-bottom.

First arm whose pattern matches and guard (if present) evaluates true is selected.


7.2.5 Binding and scope

Bindings introduced by a pattern are in scope within that arm’s block (and guard, if you allow guard to reference them).

Bindings shadow outer names (either allowed with warning, or error — your choice).


7.2.6 Exhaustiveness (normative)

A match is exhaustive if the set of patterns (ignoring guards, or treating guarded arms as partial) covers all possible values of the scrutinee type.

For enums: all cases must be covered (including payload shapes). This is the standard exhaustiveness property Rust enforces. 

For unions (A|B|C): all alternatives must be covered by patterns.

For integers: exhaustiveness is only provable with else unless you support interval analysis.


If not exhaustive and no else, it is a compile-time error.

7.2.7 Unreachable arms (normative)

An arm is unreachable if all values it could match are already matched by earlier arms (again, conservatively accounting for guards). Emit compile-time warning or error.

7.2.8 Refutable vs irrefutable patterns

Define:

Irrefutable patterns: always match (e.g., _, name, tuple of irrefutable patterns).

Refutable patterns: may not match (e.g., Some(x), Case(...), literal patterns).


Rules:

let Pattern = expr requires irrefutable pattern.

match allows both.


(You can align this with Rust’s conceptual split even if you name it differently.) 

7.3 Examples

7.3.1 Exhaustive enum match

enum Option[T]:
    Some(value: T)
    None

fn f(x: Option[i64]) -> i64:
    match x:
        case Some(v):
            return v
        case None:
            return 0

7.3.2 Guards and partial coverage

match x:
    case Some(v) if v > 0:
        return v
    case Some(_):
        return 0
    case None:
        return -1

7.3.3 Or-patterns

match token:
    case Plus | Minus:
        return "additive"
    else:
        return "other"


---

Recommended “minimum bar” to document as required

If you want Simple’s match to be a strong differentiator:

1. Exhaustiveness checking for enums and unions (A|B|...) 


2. Unreachable-arm diagnostics


3. Guards (if)


4. Nested destructuring for enum payloads + structs


5. else as the explicit “I don’t want exhaustiveness proof”



If you paste the exact current match syntax from your spec (or a few examples from the repo), I can rewrite the above to match your precise tokens and indentation rules without inventing any syntax.
