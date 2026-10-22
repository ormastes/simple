# Indirect callback return type and owner (#2980)

Status: source repair; runtime qualification pending. No compiler construction,
SSpec execution, or native execution was performed for this change.

## Bound evidence

C35 producer `96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`,
source `a2a52f8b836d0ec453aa3b4f527555d5d8f4d9f3`, compiled the parenthesized
function-field fixture. ARM execution returned 14: bool/i64 callbacks and the
record status field passed, but the two text fields failed. Retained evidence:
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c35-callback-field-workaround/arm/`
(`fixture`, `fixture.sha256`, `run.status`, `check-port.disasm`). The indirect
record call at `0x129b00` is followed by a status read at `0x129b20`; both text
reads use field zero at `0x129b58`. This is evidence about that old producer,
not runtime evidence for this patch or imported-owner fixtures.

## Cause and repair contract

The generic end of `lower_call` lowered the callee's entire Function type as
the return type, then omitted the return provenance retained by direct calls.
It now extracts the declared Function return, uses the existing text handle
representation, and retains HIR type and the exact declaration's registered
record layout. Explicit unresolved return types produce a fatal diagnostic;
an untyped legacy call does not acquire an invented owner. Word parameter
marshalling and raw-function/capturing-closure dispatch are unchanged.

Function-valued fields introduce a second ownership boundary: their named
return SymbolId belongs to the provider's symbol table. The field prescan
records that return declaration's ownership key. Importer projection rebinds
the return using the existing qualified type index, validates canonical owner,
and only then permits a checked short-name lookup. A missing owner or a
same-name competitor cannot authorize a foreign raw ID. This change covers
an immediate Named callback return; it does not redesign generic/container
signature relocation or argument ABI.

`lower_call_with_value(callee, args, prelowered_callee)` shares the existing
argument conversions with the method-field repair owned in a separate change.
An already-projected callable bypasses direct/IIFE/bitfield interpretation and
is not lowered again. The ordinary wrapper passes nil. Method-field selection
itself is not repaired in this commit.

## Authored regressions and remaining gates

`test/01_unit/compiler/mir/indirect_call_return_owner_spec.spl` checks real field
prescan and qualified rebinding with colliding IDs, missing-owner rejection,
actual MIR call result type/layout, unresolved-result rejection, and that an
already-projected field does not revisit an invalid receiver.
`test/fixtures/compiler/indirect_call_return_owner/` checks dynamic bool/i64,
record text fields, imported alias/same-basename owners with different layouts,
and a captured record-returning closure without an identity workaround.

Both suites are unexecuted. A coordinated changed-source producer must compile
and run the fixture, with source/producer/backend/runtime/cache receipts, before
claiming correctness. Full compiler/library checks, MCP smoke, whole tests,
ARM/RISC-V qualification and Phase 3 remain pending. Bug DB reconciliation is
pending an admitted pure-Simple tooling runner.
