# MIR canonical reverse lookup: source evidence, runtime UNRUN

Base: `20128a8a9e6df70afd66353c7533734055ec61df`. Its compiler source equals
`380200890ff030b34c68ff38f362b482e1276769`; this packet does not modify the
immutable live Phase 3 source, producer, process, cache, or bootstrap modules.

## Concrete waste and change

`MirLowering.mir_struct_symbol_name` previously copied
`canonical_type_symbols.keys()` and reverse-scanned the entire canonical
inventory whenever the active HIR SymbolTable lacked the MIR symbol. For K
canonical types and Q such lookups that creates Q key arrays and can visit
K*Q rows. This is a concrete source hotspot, not evidence that it dominates
the currently running compiler.

The existing per-invocation map now has an ID-to-key inverse. All three
original mint sites use one allocator helper, retaining their original key
normalization, lookup-before-mint behavior, increment, IDs and insertion order.
The inverse is promoted with the forward map and copied in both directions
at the nested lowerer boundary. Named HIR types, repaired direct struct return
types and array record element types therefore use the same existing identity.
SymbolTable lookup still precedes the inverse. Class membership remains a
lookup-time decision, so the inverse stores canonical keys, not display names.

For ordinary minted symbols, each lookup performs a hash-table inverse
lookup and no inventory scan or key snapshot: expected O(K+Q) indexing/lookup
work, excluding string processing. The inverse retains O(K) additional key
references and dictionary slots. Peak/steady RSS and lookup overhead remain
unmeasured. Missing IDs retain the old slow scan. A pre-seeded legacy map is
searched in its original first-match order and the found key is cached.
Arbitrary external mutation of an already indexed forward map is not a
supported compiler path; the source audit found no such writes.

## Regression packet

`test/05_perf/compiler/mir_canonical_type_reverse_lookup_spec.spl` calls the
actual production allocator and lookup methods. It covers unchanged dense IDs,
existing-key reuse, all three mint routes, SymbolTable precedence, class
membership changes, fresh-invocation state and legacy duplicate-ID order.
The 256-type/two-pass workload would visit 65,792 inventory rows with the old
lookup (sum of positions over each complete traversal). It asserts zero rows
in the actual production fallback-loop counter, alongside differential keys
from the former scan oracle. These are executable assertions, not executed
measurements. The two nested transfers and transient promotion are reviewed
source wiring; this packet does not claim executed nested-body coverage.

| Check | Evidence status |
|---|---|
| Whitespace/diff integrity | PASS: `git diff --check` |
| All forward-map writers and nested transfers | Source audited; Astra review pending |
| Focused regression execution | UNRUN: no admitted test-capable runner assigned |
| Compiler/lib/MCP checks, optimizer, smoke checks | UNRUN: same admission constraint |
| Before/after elapsed p50/p95 and peak/steady RSS | UNRUN; no speed or joint performance PASS |
| Current live producer includes this fix or existing provider optimization | UNPROVEN |

The provider session/demand optimization from PR3830 is already in this base;
this change does not reapply it. Admission-time source hashes do not establish
what the live producer compiled. Runtime admission and root-owned scheduling
remain prerequisites to any compile, measurement, publication or release claim.
