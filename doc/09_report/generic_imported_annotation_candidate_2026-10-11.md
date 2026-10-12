# Imported generic annotation preservation

STATUS: UNQUALIFIED; executable checks and native fixture are UNRUN.

A bounded source audit found two concrete erasure paths remaining after nominal
transport: imported Enum/Trait instances returned Any even when their declaration
and arguments resolved, and invalid imported arguments caused all newly recorded
diagnostics to be removed. Thus `Box<NotInScope>` was silently accepted while
the plain `NotInScope` annotation was rejected. Existing tests explicitly pinned
that unsafe recovery; they now require the same argument preservation and
diagnostics as local declarations.
Malformed imported class, enum, and trait argument regressions are prepared.

The change routes resolved enum/trait instances through the existing named type
lowering, which already retains their arguments for local declarations. It also
keeps argument/base diagnostics rather than withdrawing them. This does not add
trait dispatch or prove generic enum payload lowering: the native fixture
`test/fixtures/bootstrap/generic_imported_enum/main.spl` must execute and print
`text=ab int=7`, with the text and integer payload operations inspected in LLVM.
Any newly surfaced unresolved import is a remaining implementation obligation,
not a reason to restore silent Any recovery.

The same bounded pass found no additional demonstrated stale-signature or
parameter/return transfer counterexample in the reviewed relocation integration.

Parent independent source review found no demonstrated P0/P1. Staged whitespace,
working/staged runtime-facade guards and numbered-artifact guard passed. No source
guard result counts as executable enum or trait qualification.
