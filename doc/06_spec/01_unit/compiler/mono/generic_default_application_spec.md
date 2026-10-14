# Complete omitted generic arguments

Requirement trace: `doc/03_plan/phase3_bootstrap_remaining_2026-10-13.md`, item 7.
Executable specification: `test/01_unit/compiler/mono/generic_default_application_spec.spl`.

The caller supplies explicit arguments first. Positional arguments and an expected
result can infer remaining bindings. An inference conflict or unknown argument
type refuses completion. Empty array/dictionary literals provide legitimate absent
element evidence: later arguments may bind it, otherwise a declared default may
fill it. An actual Ok/Err enum value can carry an Infer placeholder for its absent
arm only; its active payload must infer a concrete type matching the active arm.
Both-arm holes and erased active payloads refuse. Its known arm still binds.
Any/Error and unresolved declaration types, including
nested erasure and nonconcrete cast/conversion targets, refuse instead of letting a
default conceal them. Defaults fill only still-unbound parameters in declaration
order. Earlier completed parameters substitute dependent defaults. Values travel
into declaration scope before completion and back into caller scope before keying.

The specification checks omitted/explicit specialization deduplication in retained
and archive-request modes, inferred precedence, sparse explicit prefixes, dependent
defaults, declaration span retention and imported nominal ownership. It checks
constructor completion against the same key as an explicit constructor. Refusals
cover excess/required/cyclic/default-filled bounded parameters, unknown arguments,
conflicts and diagnostic priority without specialization requests.
An archive call-rewrite assertion checks one concrete function signature and cleared
call type arguments for omitted and equivalent explicit calls. Unknown types at
unrelated concrete argument positions retain the earlier inference behavior.
Depth refusal (`E-MONO-030`) precedes new completion errors; missing nominal owner
identity preserves `E-MONO-041`. Default return transport failure reports
`E-MONO-042` and cannot publish a specialization/request. Completion refusals carry
`E-MONO-032`, including nominal constructors. Existing nominal transport caches
may install rows while successful evidence transport occurs; this is distinct from
publishing specialization symbols.

Native fixtures are `test/fixtures/compiler/generic_default_application/main.spl`
(expected exit 0), `conflict.spl` and `missing.spl` (expected compiler refusal).
Native execution and specialization metadata assertions are both necessary: phantom
type parameters alone make returned values insufficient proof of a completed key.

Runtime execution: **UNRUN; admission BLOCKED**. No eligible full pure-Simple test/native-build CLI is
available in this session. The retained pure producer's compiler-module closure
failed in earlier exhausted cycles. No Rust-seed test substitution, source-pattern
equivalence claim, native PASS or generated-manual claim is made here. The source
specification and native fixtures are authored, unexecuted assertions.

Scope: default-filled bounds fail closed pending trait-obligation validation.
Complete supplied bounded arguments retain the prior policy. Existing owner-method
lookup and named annotation/field gates require full arity; omitted annotation
arguments are not independently normalized by this bounded constructor/function
change. The broader language-default feature requires those paths and native
qualification before it can be marked complete.
