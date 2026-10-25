# Static lock-level checker detail design

Status: foundation design; verify the final implementation against this contract.

## Annotation and diagnostics

`@lock_level(n)` accepts exactly one nonnegative integer literal representable
as i64. Missing, duplicate, negative, overflowing, named, expression-valued or
extra arguments fail. Supported targets are named synchronous functions and
proved immutable module-level Mutex resources. Other declaration kinds fail
rather than dropping metadata. An annotation on an asynchronous function is not a
synchronous ranked scope and must be rejected until suspension effects exist.

| Code | Meaning |
| --- | --- |
| E-LOCK-LEVEL-001 | Invalid or duplicate annotation |
| E-LOCK-LEVEL-002 | Entered rank is below an already held rank |
| E-LOCK-LEVEL-003 | Scope, identity, effect or lifetime cannot be proved |
| E-LOCK-LEVEL-004 | Attempted exemption has no verified review authorization |

Source text alone is not a reviewed exception. `@unsafe` does not suppress the
ordering rule. No exception schema is fabricated in this foundation.

## Shared interface and state

The public arena checker is `check_lock_level_order() -> text`, with empty
text denoting success. Error line/column accessors follow the existing captured
write check convention. Parser metadata is keyed by declaration ID and reset
per parse. Suggested private responsibilities are
`lock_level_annotation_value`, `lock_level_enter`, and `lock_level_leave`;
implementation may split these while preserving one canonical policy owner.

Collect valid ranked declarations before walking calls. Walk local direct
calls through unannotated wrappers with the incoming held maximum. Enter a
callee's rank before its body, then restore the caller's state on return.
Sibling calls do not retain each other's rank. Distinguish visiting from
completed states; a cycle must terminate with a conservative diagnostic or
a proven fixed point. Any analysis bound is explicit and fails closed.

Every statement and expression that can contain a call must either be visited
or rejected in a checked scope. Cover conditions, branch bodies, return
expressions, arguments, default expressions, loops, collections, match arms
and guards, short-circuit expressions, and nested declarations. Analyze call
arguments in the caller context before entering the callee's scope. A lambda
declaration does not execute its body. Callback invocation needs a supported
contract; do not execute every lambda statically at its lexical declaration.

## Integration invariants

Native parsing, native cached AST restoration, and interpreter admission
must all reject the same bad program before lowering or evaluation. Unknown
extern/imported calls inside a scope cannot assume no lock effect. A module
without rank annotations retains its existing behavior, but is not certified
for calls into separately compiled annotated functions without effect metadata.

Tests must prove metadata survives the selected cache strategy and that two
successive parses cannot leak levels, errors or declaration IDs between modules.
Transient arena retirement must not leave dangling annotation arrays.

## Physical callback scopes

Retain resource rank separately from function rank and validate the declaration
kind when reading cache metadata. An immutable module-level Mutex resource can
carry the same existing annotation. Its declaration identity, canonical import
ownership and constructor establish the resource fact. Initial support requires
explicit canonical imports and `mutex_new`; aliases, glob imports and configured
generic `std` paths remain unproved. A shadowed name or mutable assignment
invalidates the resource fact rather than retargeting another lock.

Represent every supported acquisition as a virtual ranked graph node keyed to
the resource declaration. Receiver/argument effects are parent-node edges; the
inline callback runs under the new node's rank. Completion returns to the parent
node. A nested callback must see the enclosing resource rank. A callback outside
the supported canonical APIs or passed by reference has unknown effects.

Same-resource re-entry fails even when ranks equal. Distinct equal-ranked
resources remain allowed under the selected rank policy, which is not a total
deadlock proof. Unknown lifetimes, manual lock operations, escaping aliases,
unresolved constructors/imports and suspension report E-LOCK-LEVEL-003 with a
remedy naming immutable resources and inline synchronous `with_lock` callbacks.

A resource-ranked module checks unknown effects in all function bodies and
module initializers, so raw operations or resource aliases outside a callback
cannot bypass the checked boundary. This intentionally rejects unsupported
code rather than certifying it. Native import ownership must be preserved.
Graph node, edge and traversal-work limits are finite; exhaustion emits E003.
This bounds conservative per-ranked-root traversal without claiming linear
complexity in the number of ranked roots.

The supported physical subset protects scalar values. The canonical constructor
must receive a scalar literal, and every callback exit must preserve a proved
scalar value. This invariant permits primitive callback-parameter arithmetic
without silently calling user-defined operators after an earlier callback
replaced the payload with a nominal object. Check every explicit return and
implicit tail, including branches; a scalar last expression alone is not proof.
Shadowing invalidates previous scalar facts, and branch-local facts cannot leak
into sibling branches. Unsupported result proofs fail E003.
