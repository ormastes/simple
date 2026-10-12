# Generic if-val payload inference candidate

STATUS: UNQUALIFIED. Executable specifications and native fixture are UNRUN.

REQ-GENERIC-IFVAL-PAYLOAD: a generic call on an if-val binding uses the payload
type retained by HIR; ordinary value-position existence checks remain optional,
and condition-position checks preserve boolean presence semantics.

The parser retains `bind_optional_payload`; HIR's binding_source_type uses it to
store the payload type in the local symbol table. HIR Let still carries the
original absent annotation, and its ExistsCheck initializer remains Optional.
Mono's collector previously ignored the symbol table and consequently installed
Optional<T> into the inference environment instead of the known payload T.

The fix consults concrete symbol-table binding evidence only for an ExistsCheck
initializer with no concrete explicit annotation. An ordinary `val x = opt.?`
has an Optional symbol type and therefore remains Optional. No runtime node or
MIR sentinel handling changes: `.?` in value position is payload-or-nil, while
condition lowering uses the boolean presence predicate.

Four unit scenarios cover payload evidence, ordinary Optional preservation,
explicit annotation priority, and real parsed text/integer payload calls through
mono. Native fixture `generic_if_val_payload` exercises present and absent text
and integers (including payload 3, the raw nil sentinel value) and bool-position
existence checks. Expected stdout is pinned beside the fixture. LLVM must show
payload specializations and correct payload arithmetic/string operations.

Remaining: if HIR still lacks a concrete payload type (for example an unresolved
generic producer result), this change does not invent provenance or silently
unwrap it. That inference obligation remains separate. No whole-H-IFVAL closure
or runtime optional qualification is claimed before successor execution.

Parent independent source review found no demonstrated P0/P1; the fixture uses
an explicit if-condition for boolean presence. Staged whitespace and
working/staged runtime-facade guards passed. Executable checks remain UNRUN.
