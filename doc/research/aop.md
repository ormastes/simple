Simple Language — Unified Predicate Grammar for AOP, Hybrid DI, Mocking, and Architecture Rules

Version: 2025-12 (concretized)

This specification defines a single predicate expression language reused across:

AOP weaving (compile-time base; optional link-time and runtime backends)

DI binding selection (hybrid DI)

test mocking selection (test-only)

architecture rules (static dependency validation)


The goals are simplicity, error prevention, and conciseness, while preserving one-pass parsing and zero overhead when not enabled.


---

1. Normative Design Principles

1. One-pass parsing

Predicate expressions appear only in SDN fields typed as pointcut: and in the in-source syntactic island pc{ ... }.

pc{...} is not a general expression value; it is permitted only after specific introducers.



2. Compile-time is the base weaving backend

Compile-time weaving must support coverage, contracts, and profiling.

Link-time and runtime backends are optional.



3. Zero overhead when not enabled

If aspects.enabled is empty, the compiler MUST emit no join-point probes and no weaving metadata.

If runtime DI is used but runtime interceptors are disabled, resolve[T]() MUST return the raw instance (no proxy allocation).



4. Manual injection is the baseline

Manual construction/wiring remains the simplest and fastest path.

DI is additive and opt-in.



5. Determinism by construction

Rule resolution order: priority → specificity → stable order.

DI MUST have exactly one winning binding per (profile, abstraction).



6. Safety rails

mock is test-only.

Mock* bindings are illegal outside the test profile.

Runtime interception in release is forbidden unless explicitly allowlisted.





---

2. Attribute Syntax (Single Form)

The language uses only:

@name or @name(k=v, ...)


System/compiler attributes are namespaced:

@sys.inject, @sys.coverage, @sys.test_only, @sys.release, …



---

3. Collision-Free Predicate Syntax

3.1 Syntactic island: pc{ ... }

pc{ ... } starts a pointcut lexical mode that ends at the matching }.

Inside pc{...}: !, &, |, *, **, .. have pointcut meaning.

Outside pc{...}: the normal language lexer/parser applies.


This prevents grammar collisions with normal operators, ranges, and multiplication.

3.2 Allowed introducers for pc{...}

pc{...} is only allowed after:

on pc{...} use <Interceptor>

bind on pc{...} -> <Impl> ...

forbid pc{...} / allow pc{...} (architecture rules)



---

4. Predicate Expression Language

4.1 Operators and precedence

NOT: !

AND: &

OR:  |

Grouping: ( ... )


Precedence: ! > & > |.

4.2 Wildcards for paths (layers/packages)

Patterns support:

*  matches one segment (e.g., hal.*)

** matches zero or more segments (e.g., hal.**)


Guidance:

** is strongly recommended for architecture layer rules.

For weaving, ** SHOULD be restricted to within(...) to avoid join-point explosion.


4.3 Minimal EBNF

expr        ::= or_expr
or_expr     ::= and_expr ( '|' and_expr )*
and_expr    ::= not_expr ( '&' not_expr )*
not_expr    ::= '!' not_expr | primary
primary     ::= selector | '(' expr ')'

selector    ::= name '(' args? ')'
args        ::= arg (',' arg)*
arg         ::= STRING | IDENT | pattern | signature

pattern     ::= seg ('.' seg)*
seg         ::= IDENT | '*' | '**' | IDENT '*' | '*' IDENT

Notes:

The meaning of selector depends on context (weaving vs DI vs arch).

pattern is used for module/type paths (e.g., services.**, hal.*).



---

5. Selector Sets by Context

The same predicate grammar is reused, but each context has an allowed selector set.

5.1 Weaving selectors (runtime join points)

Compile-time (base):

execution(signature)

within(pattern)

attr(IDENT)

effect(effect_set)

test(IDENT)

decision() / condition() (compiler-defined)


Link-time (optional):

adds call(signature) (boundary-level instrumentation)


Runtime (optional, DI-proxy boundary):

may add init(pattern) only for container-controlled construction


Deferred:

get/set join points (high volume; tooling complexity)


Signature pattern (minimal)

signature   ::= ret_pat ' ' qname_pat '(' arg_pats ')'
ret_pat     ::= '*' | pattern
qname_pat   ::= pattern
arg_pats    ::= '..' | (arg_pat (',' arg_pat)*)?
arg_pat     ::= '*' | pattern

5.2 DI binding selectors (static selection)

DI predicates may use only:

type(pattern)

within(pattern)

attr(IDENT)


DI predicates MUST NOT use join-point selectors (execution/call/decision/condition).

5.3 Mock selection selectors (test-only)

Same allowed selectors as DI: type/within/attr.

5.4 Architecture selectors (static program graph)

Architecture rules use an ARCH selector namespace:

import(from_pattern, to_pattern)

depend(from_pattern, to_pattern)

use(pattern)

export(pattern)

config(STRING)

plus within(pattern) and attr(IDENT)



---

6. Weaving Backends

6.1 Compile-time weaving (Base)

default supported backend

deterministic instrumentation in HIR/MIR

best optimization and source mapping


Hard rule: if aspects.enabled = [], emit no probes and no weaving metadata.

6.2 Link-time weaving (Optional)

cross-module boundary instrumentation

enables call(signature) at boundary level


6.3 Runtime weaving via DI proxies (Optional)

interception only at DI proxy boundaries

enables around with proceed()


Hard rule: if runtime interceptors are disabled, resolve[T]() returns raw instances (no proxies).


---

7. Advice Forms, Ordering, and Safety

7.1 Advice forms

before

after_success

after_error

around (runtime; optionally restricted compile-time around on execution only)


7.2 Ordering

Advice ordering is controlled by aspect.priority:

higher priority executes earlier for before

higher priority executes later for after_*

for around, higher priority wraps outermost

ties break by stable lexical order


7.3 Proceed safety rules (runtime)

around MUST call proceed() exactly once (enforced by compiler or runtime verifier).



---

8. Hybrid DI (Selected)

8.1 Manual injection baseline (zero overhead)

fn main():
  let cfg = Config.load()
  let repo = SqlUserRepository.new(cfg.db)
  let svc  = UserService.new(repo)
  run_server(svc)

8.2 Hybrid model

compiler builds a typed dependency graph

SDN selects implementations per profile

release may freeze profile and emit direct wiring


8.3 SDN schema (minimum)

di:
  mode: hybrid
  profiles:
    <profile_name>:
      - bind on pc{ <di_predicate> } -> <ImplType> scope <Scope> priority <int>

Where <di_predicate> uses only type/within/attr.

8.4 Constructor injection (selected behavior)

Constructor-level injection (preferred)

class OrderService:
  repo: OrderRepository
  clock: Clock

  @sys.inject
  fn new(repo: OrderRepository, clock: Clock) -> Self:
    return Self { repo: repo, clock: clock }

Rules:

@sys.inject on a constructor means all parameters are injectable.

If any parameter is not resolvable, compilation fails with a parameter-level diagnostic.

Do not mix constructor-level @sys.inject with per-parameter injection attributes.


Per-parameter injection (allowed)

fn new(@sys.inject repo: OrderRepository, @sys.inject clock: Clock) -> Self:
  ...

8.5 Deterministic binding resolution

For each (profile, abstraction):

1. collect matching binding rules


2. choose highest priority


3. tie-break by specificity


4. tie-break by stable file order



If still tied: compile error.


---

9. Mocking (Selected: Trait-boundary, Test-only)

9.1 Mock declaration

@sys.test_only
mock ClockMock implements Clock:
  expect now() -> Time:
    return Time.from_unix(0)

Hard rules:

mock is illegal outside test/.

binding Mock* is illegal outside the test profile.


9.2 Applying mocks without weaving

Mocking is performed via DI binding selection, even when AOP weaving is disabled.

profiles:
  test:
    - bind on pc{ type(Clock) } -> ClockMock scope Singleton priority 100


---

10. Architecture Rules (Selected: Uses the Same Predicate Grammar)

10.1 In-source rules

arch_rules:
  forbid pc{ import(within(domain.**), within(infrastructure.**)) | depend(within(domain.**), within(infrastructure.**)) }
  forbid pc{ use(Container) & within(domain.**) }
  forbid pc{ config("profiles.test") & attr(release) }

10.2 SDN validation hooks

Architecture checks MUST validate SDN policy:

release build MUST NOT select test profile

release build MUST NOT enable runtime interceptors unless allowlisted



---

11. Priority and Specificity

11.1 Priority

higher integer wins

applies to DI bindings, mock bindings, and arch allow/deny rules


11.2 Specificity (tie-break)

Recommended scoring (higher is more specific):

literal qname segment: +2

prefix/suffix wildcard segment (foo*, *bar): +1

single-segment wildcard *: +0

multi-segment wildcard **: -2

negation !: -1



---

12. Required Diagnostics (Error Prevention)

The compiler/test tooling MUST provide:

1. Ambiguous DI binding

list all matching bindings

show priority and specificity

suggest narrowing (type(...), within(...)) or adjusting priority



2. Illegal selector in context

e.g., execution(...) in DI predicate

suggest allowed selectors for that context



3. Illegal mock in non-test

point to mock declaration or Mock* binding

suggest moving to test/ or restricting to test profile



4. Runtime interception in release (unless allowlisted)




---

13. Minimal Implementation Plan

1. Implement pc{...} lexical island and the predicate parser.


2. Implement context validation tables for selector sets (weaving vs DI/mock vs arch).


3. Implement hybrid DI binding resolution (priority/specificity/uniqueness).


4. Implement constructor injection with @sys.inject (all params injectable).


5. Implement mock lowering for mock implements Trait (test-only).


6. Implement architecture rule engine (ARCH selectors) + SDN validation.


7. Implement compile-time weaving join points (execution/decision/condition).


8. Add optional link-time call(signature) and optional runtime DI-proxy around.




I improved and tightened the spec on the canvas into a more normative, collision-safe, and implementation-ready Markdown document.

Key upgrades applied:

Clear MUST/SHOULD rules (error-preventing, unambiguous behavior).

Formalized the pc{...} syntactic island and restricted where it can appear (prevents grammar collisions).

Added a minimal EBNF for expressions, patterns, and signature patterns.

Made selector sets explicit by context (weaving vs DI/mock vs arch) so misuse becomes a compile error.

Implemented your choice for constructor-level @sys.inject: valid only if all parameters are injectable, otherwise parameter-level diagnostic.

Strengthened “AOP not enabled” semantics: DI/mock/arch can still use predicates while weaving emits zero probes/metadata.

Kept hybrid DI selected, and enforced determinism with priority → specificity → stable order, plus unique DI binding rule.


You can copy the full Markdown directly from the canvas titled: “Simple Language — Unified Predicate Grammar for AOP, Hybrid DI, Mocking, and Architecture Rules”.
