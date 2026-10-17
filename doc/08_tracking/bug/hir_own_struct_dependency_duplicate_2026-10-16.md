# Own struct dependency allocates a second nominal declaration

Status: source repair and focused regression added; qualified native execution pending.
Bug database reconciliation: pending; this repair session has no qualified bug database runner.

Observed producer: provisional pure-Simple Phase2 d6c3e3758c6dcc548e5fe3b4bb86aa6b8d997ceb7a5a9aee183156775e01523d, source f46941a142c.
Evidence: `C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase4-mcp-d6c3-cycle1/tmp/native-build-stderr-16884-1.log`.
MCP MIR lowering reports `Optional record has ambiguous current provider declaration` at `src/lib/nogc_sync_mut/database/wal.spl:256:19`, when matching the stored result of `wal_entry_from_line` returning `WalEntry?`.

Own struct declarations were absent from the qualified type index. Only classes
are indexed automatically by SymbolTable allocation, and the declaration pass
explicitly indexed enums. Later callable/field dependency materialization can
allocate a second imported struct with the same declaration owner and name.
The Optional payload's ambiguity rejection correctly refuses two distinct IDs.

Imports run before own declarations. The own-struct allocator now adopts an
already qualified same-owner dependency after validating its stored ID, kind,
name and owner; it rebinds the lexical spelling without allocating or merging
IDs. A distinct same-owner lexical declaration remains an error.
The declaration pass also publishes each own struct and bitfield after validating
its kind, name and owner. Existing conflicting qualified IDs remain errors;
first-write ownership is never overwritten. The focused regression checks
own declaration publication, same-owner imported dependency reuse without
allocation, Optional payload resolution, and genuine qualified conflict rejection.
The existing Optional duplicate-provider rejection is unchanged.

Additional source regressions cover dependency-first ordering, repeated own
declaration idempotence, and bitfield publication. The synthetic local used for
Optional lookup checks the ownership contract only, not generated payload
execution. Generic struct arguments remain separate HIR type arguments: this
repair indexes their declaration, not a specialized instance or field layout.
Distinct owners remain distinct qualified keys. Type aliases are untouched.
No native reproduction proves yet which declaration order produced the observed
MCP duplicate; the repair covers both dependency-before-declaration and
declaration-before-dependency orders without relaxing the ambiguity guard.

This does not resolve the separate four Option bare-name collision diagnostics
in the same MCP failure. No successful MCP build or deployment is claimed.
