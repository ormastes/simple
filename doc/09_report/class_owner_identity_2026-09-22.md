# P3 class owner identity verification

STATUS: WARN — implementation draft; native/self-hosted acceptance blocked.

The available executable at
C:/Users/ormas/dev/simple/bin/release/x86_64-pc-windows-msvc/simple.exe prints
Simple Language v1.0.0-rc.1 and explicitly identifies itself as a Rust-built
bootstrap seed. It was queried for version only and was not used to run the
acceptance tests. No admitted pure-Simple runtime was available in the campaign.

Consequently, the unit spec, native fixture, compiler/lib/MCP/LSP checks,
MCP integration/native smoke, and Windows/other-host codegen execution are
NOT RUN. Real lookup elapsed time and peak RSS are also NOT MEASURED.

Source review covers provider/consumer ID boundaries, canonical and raw layout
aliases, nested Named types, helper and method default relocation, lazy capture
errors, callable linkage, entry-main context, and transient roots. The added
tests and fixture are executable test sources, not claimed passing evidence.

The new helper rejects unsupported provider default shapes at omitted-field
use sites. Explicit field values remain usable. Remaining supported-shape
expansion must preserve the same relocation and failure contract.

Static source env/process guard (`--working`): PASS. Initial tracked diff
whitespace check: clean. A source-invariant check found a remaining per-function
SymbolTable reset in the nonflat-extra path; it was removed before the final
static pass. Branch coverage is not measured.

Final static source/layout assertions: 13 PASS. Staged env/process guard: PASS.
Staged whitespace check: clean. Independent review found ownerless bootstrap
link lookup and raw function-value naming defects; these were fixed together
with the direct-call path that bypassed symbol_to_operand. Seven focused source
assertions for those fixes pass. The executable unit/native controls were
extended for ownerless ABI symbols and local/imported first-class functions.
The final independent focused structural review found no additional concrete
blocker in those paths; it did not execute or compile the changed sources.

These are source checks, not language execution or codegen receipts. The draft
must not be promoted to release or represented as production verified without
the missing runtime, ABI, and performance evidence.
