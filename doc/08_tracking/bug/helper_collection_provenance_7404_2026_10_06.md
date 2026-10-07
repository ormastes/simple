# Native helper collection provenance remains unqualified

Producer `7404ff60a2fe6681add7df34bcd79f9b45c1fe4843c1c22289316e4bcd5d79e8`
against source `606f4752742051b858bb6800e461d367910c9533` failed both retained-HIR
helper builds. The generator retained 56 diagnostic events and main-verdict 24,
with no dropped or truncated events. Neither helper executed.

Both report `#143` with collection MIR type `I64` but no source location. The
generator also reports unresolved `get` and `insert` at collection_feedback.spl
15:69. HashMap is a concrete text-to-text class, and the affected ordinal local
already has an explicit HashMap annotation. This is not evidence that generic
collections or for-in syntax are unsupported. The exact failed loop and the
class-method loss remain unlocated. The detailed retained trace shows that the
Windows environment tuple loop and signal-handler tuple-array loop lower their
bodies, so they must not be blamed solely from the summary diagnostic.

The staged candidate fills one narrow MIR provenance gap: for-in currently
consults only the lowered-local HIR side table. When that table has no entry,
the candidate also consults the iterable expression's declared HIR type.
Existing Array/Slice/Str checks and the erased-I64 guard remain authoritative.
An arbitrary integer or dictionary is still rejected. No loop is replaced,
no check is disabled, and no class-method fix is claimed.

The diagnostic retains the original failure prefix, adds its module owner,
passes a known expression span when the for-statement span is empty, and uses
the existing driver formatter. If neither span survived, the formatter states
`<source span unavailable>` explicitly. Error fatality and runtime panic
behavior are unchanged.

## Focused evidence and remaining checks

The authorized seed `15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`
executed the exact extracted production diagnostic formatter with six checks:
file/line/column, line-only, absent span, empty span, unrelated message, and
unchanged fatal flag. Exit 0. The standalone declared-container fixture and
optional concrete-class fixture also exited 0. Initial fixture checks incorrectly
called an unimported `assert` function; cycle two replaced those calls with the
same predicates returning nonzero main status on failure. No production
assertions were removed. No green check was rerun.

These seed results establish fixture semantics and formatter behavior only.
The modified MIR lowerer has not been built or executed. Required native checks:

- Compile and execute `for_declared_collection_provenance/main.spl`: exit 0.
- Compile and execute `optional_class.spl`: exit 0, preserving ordinals 0 then 1.
- Reject `reject_integer.spl` before code generation with #143 and its location.
- Rebuild the bounded helper prerequisites only after focused native checks.
  A continuing failure must include its module/span; do not infer a fix from
  the seed result or remove the failing construct.

Evidence packet: `helper-collections-7404-repair/focused-results.json` under the
Windows restart runtime evidence root. Native qualification and causal repair
of the original helper errors remain pending.
