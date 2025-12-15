Below is a rewritten, self-contained Contracts specification for Simple, updated to your requirement: no signal keyword. Instead, functions return a union like (i64 | DivByZero).

This document defines language support, grammar, static rules, runtime semantics, and refinement types (compile-time when provable, runtime otherwise). It also includes complete examples.


---

Contracts Specification for Simple

1. Scope and goals

Contracts provide:

Preconditions (in:): requirements on inputs and ambient state before execution.

Routine invariants (invariant: inside a function): properties that must hold at function entry and exit.

Postconditions (out(ret):): properties that must hold when the function returns a success value.

Error-postconditions (out_err(err):): properties that must hold when the function returns an error value in a union return type.

old(expr): snapshot values at function entry to use in postconditions.


Contracts are intended to be:

Readable and ergonomic for humans and LLMs.

Checkable at runtime with controllable overhead.

Partially checkable at compile time via refinement types (where) and basic proof/range propagation.



---

2. Contract blocks and meaning

2.1 Contract sections

A function body may include these contract sections:

in:
A list of boolean expressions (preconditions). All must be true at entry.

invariant:
A list of boolean expressions (routine invariants). All must be true:

after in: passes (at entry), and

again at every exit (both success and error exits).


out(ret):
A list of boolean expressions (postconditions for success exit). Evaluated only when the function returns a success value. The identifier ret binds to that success value.

out_err(err):
A list of boolean expressions (postconditions for error exit). Evaluated only when the function returns an error value. The identifier err binds to the error value (one of the union’s error alternatives).


2.2 Union returns: success vs error

Simple uses union return types of the form:

(T | E) for one error type, or

(T | E1 | E2 | ...) for multiple errors.


A function can return:

return <T> — a success value

return <E> — an error value (must be one of the union alternatives)


Classification rule:

If the returned value has type T, it is a success exit.

If the returned value has type Ei, it is an error exit.


out(ret): applies only to success exits.
out_err(err): applies only to error exits.

2.3 old(expr)

old(expr) evaluates expr once at function entry (after in: succeeds) and stores a snapshot. It may be referenced in out(ret): and out_err(err):.

Restrictions (v1, implementable):

old(expr) is allowed only when expr is snapshot-safe:

primitive scalars (ints, bool, enums)

immutable value structs

or types marked @snapshot (compiler-defined snapshot semantics)




---

3. Purity constraints for contract expressions

All expressions inside in:, invariant:, out(ret):, out_err(err): must be pure:

Allowed:

arithmetic, boolean, comparisons

field/array reads

calls to functions marked @pure (or proven pure)


Forbidden:

assignments or mutations

I/O, logging, syscalls

actor sends, locks, thread operations

random / time-based nondeterminism

any call not marked/proven @pure


Violation is a compile-time error.


---

4. Runtime semantics and check ordering

Let function f be called, with optional contract sections.

4.1 Entry checks

1. Evaluate all in: expressions.

If any false → ContractViolation.Pre is raised.



2. Snapshot all referenced old(...) values (after preconditions pass).


3. Evaluate all routine invariant: expressions at entry.

If any false → ContractViolation.InvariantEntry.




4.2 Exit checks (success or error)

On any exit (either return T or return E):

4. Evaluate routine invariant: expressions at exit.

If any false → ContractViolation.InvariantExit.



5. If success exit (T):

Bind ret to the returned T.

Evaluate all out(ret): expressions.

If any false → ContractViolation.Post.



6. If error exit (E1|E2|...):

Bind err to the returned error value.

Evaluate all out_err(err): expressions.

If any false → ContractViolation.ErrPost.




4.3 Build modes (compiler option)

The compiler controls contract checking:

--contracts=off
No checks emitted.

--contracts=boundary
Checks emitted only for:

public/exported functions, and/or

module boundary calls (implementation-defined).


--contracts=on
Checks emitted for all functions with contract sections.

--contracts=test
Same as on, plus richer diagnostics (e.g., expression text, file/line, captured values).



---

5. Type and class invariants

5.1 Declaration

A class or struct may declare a type invariant:

class Account:
    balance: i64

    invariant:
        balance >= 0

5.2 When type invariants are checked

Type invariants are checked:

On entry and exit of public methods of the type, and optionally

At module boundaries where values of that type cross an API boundary (in --contracts=boundary mode).


Type invariants are conceptually separate from routine invariants. A function may declare its own invariant: even if the type already has one.


---

6. Grammar

6.1 Function with contract sections

Indentation-based blocks; contract blocks appear in fixed positions:

in: and invariant: appear at the start of the function body.

out(ret): and out_err(err): appear at the end of the function body (after statements).


6.2 EBNF-ish grammar

FnDecl          := "fn" Ident "(" Params? ")" RetType ":" NL INDENT FnBody DEDENT
RetType         := "->" Type

FnBody          := EntryContracts? Stmt* ExitContracts?
EntryContracts  := PreSection? RoutineInvSection?
PreSection      := "in" ":" NL INDENT BoolExpr+ DEDENT
RoutineInvSection := "invariant" ":" NL INDENT BoolExpr+ DEDENT

ExitContracts   := (PostSection? ErrPostSection?)
PostSection     := "out" "(" Ident ")" ":" NL INDENT BoolExpr+ DEDENT
ErrPostSection  := "out_err" "(" Ident ")" ":" NL INDENT BoolExpr+ DEDENT

BoolExpr is restricted by the purity rules in §3.


---

7. Refinement types (where) with “compile-time if possible”

7.1 Syntax

Refinements attach predicates to a base type:

type PosI64 = i64 where self > 0
type NonEmptyStr = Str where len(self) > 0

7.2 Meaning

T where P(self) is a subtype of T.

Assigning a T to a T where P requires satisfying P.

Passing an argument x: T into a parameter of type T where P requires proving P(x).


7.3 Proof strategy (v1)

The compiler attempts to prove refinement predicates using:

constant folding

range/interval propagation

branch-condition narrowing (flow-sensitive typing)

simple arithmetic reasoning (implementation-defined)


If the predicate cannot be proven, the compiler inserts an equivalent runtime check at the boundary (treated like a precondition).

This achieves “compile time as possible” without requiring an SMT solver in v1.


---

8. Examples

8.1 Success + error union with postconditions

struct DivByZero:
    msg: Str

fn div(a: i64, b: i64) -> (i64 | DivByZero):
    in:
        true

    invariant:
        true

    if b == 0:
        return DivByZero(msg: "b must be non-zero")

    let q = a / b
    return q

    out(ret):
        old(b) != 0
        ret * b == a   # for exact division cases only; real specs may be weaker

    out_err(err):
        err.msg != ""
        old(b) == 0

8.2 Refinement types remove checks when provable

type NonZero = i64 where self != 0

fn div_nz(a: i64, b: NonZero) -> i64:
    in:
        true

    let q = a / b
    return q

    out(ret):
        b != 0

Here, in many call sites the compiler can prove b != 0 and omit any runtime contract checks.

8.3 Function-level invariant + type invariant

type Amount = i64 where self >= 0

class Account:
    balance: i64

    invariant:
        balance >= 0

    fn withdraw(amount: Amount) -> (i64 | Str):
        in:
            amount <= balance

        invariant:
            balance >= 0   # routine invariant (redundant but allowed)

        if amount > balance:
            return "insufficient funds"

        balance -= amount
        return balance

        out(ret):
            ret == old(balance) - amount
            ret >= 0

        out_err(err):
            err != ""
            old(balance) >= 0


---

9. Implementation notes (normative constraints)

Contract expressions must be pure (§3).

old(...) snapshots occur after successful preconditions (§4.1).

out(ret) and out_err(err) are evaluated only on their corresponding exit paths (§2.2).

Contract checking is controlled by build mode (§4.3).



---

If you want, I can now integrate this directly into your repo’s documentation style (matching the existing Simple spec format) and also define the standard library helper types and idioms you’ll likely want with union returns (e.g., is_err(x), unwrap(x), match patterns) so contract code stays compact.
