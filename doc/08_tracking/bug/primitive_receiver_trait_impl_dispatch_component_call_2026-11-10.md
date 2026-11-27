# Named-call receiver return-width component

The Rust interpreter represented a signed function result as `Value::Int` and
then selected the i64 trait impl for `getter().width()`, even when the actual
function declares `-> i32`. The method dispatcher now reads conservative return
metadata before evaluating the receiver. It uses an actual lexical Function
binding, or one unambiguous undecorated/non-generic named definition with matching
mirrored binding. Unknown callable shapes and ambiguous overloads keep the
existing fallback. Metadata lookup never evaluates arguments or the getter.

This payload contains only the named-call component. Field receivers remain
unresolved: the existing field-call path creates an untyped temporary before the
method dispatcher. All attempted field metadata/state/hooks are omitted. This
does not close the primitive receiver bug family, qualify other widths, or prove
JIT/native/full Simple CLI behavior.

Actual verification used the real Rust Parser → `interpreter::evaluate_module`
integration harness, with the same three-test fixture bytes at source
`73527aac9ca6b352c3160f99f8dd94ee6d997d34`. The baseline executed three tests:
controls passed; field failed assertion11; call failed assertion13. Cycle8
compiled successfully and executed three tests: call and controls passed; field
still failed assertion11. The call case checks that the effectful getter updates
a shared Counter exactly once and selects the i32 impl. Controls include direct
i32/i64, wide field/call fallback, local function shadowing, ambiguous overload
fallback, and a surviving wide instance across class-name rebinding.

The original cycle8 aggregate is **2 PASS / 1 FAIL**, not a green suite. Its failed
field test stopped before its later lifecycle assertion, so that assertion is
unverified. Raw failed-suite output, exact source/fixture and actual executable
bytes are preserved in the isolated control directory. The executable SHA256 is
`b5adcab8ae8d22ab9b4167a0c0404514d4e104b5ef2f94d5a1a8356a7db67c17`.

The final fixture retains the original filename, common helper and two actually
passing test bodies byte for byte, omitting the failed field test and changing
only its introductory comment. The final call helper file is byte-identical to
the executed source. The other production file differs from executed source only
by removal of the failed field metadata match arm. Consequently final whole-file
hashes are **unexecuted**; admission requires explicit source/fixture equivalence
review, not a claim that this final two-test file was run. No test or build rerun
was performed for this partition. Full compiler/core/MCP qualification remains
unrun because the qualified normal self-hosted CLI is unavailable.

The original six-cycle budget and subsequent bounded two-cycle exception are
retained. Cycle6 failed compilation with five E0433 owner paths; cycle7 reviewed
that five-reference correction; cycle8 produced the actual partial result above.
This payload partitions the already passing call component without another field
repair, helper rerun, baseline rerun, or budget reset.
