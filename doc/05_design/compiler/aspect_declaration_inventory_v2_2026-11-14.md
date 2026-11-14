# Parser advice declaration inventory V2

Status: source under review; eleven authored specs UNRUN. No complete aspect-category
or native qualification claim.

The existing effective registry uses last-wins `(path, handler)` claims. Its only
production declaration caller is the FlatAstBridge `__advice_decl` decoder. That
bridge also runs for replay/derived AST work and cannot prove original source
multiplicity. It remains unchanged.

The actual `enum_module_body` decorator emission now separately appends typed
`AspectDeclarationRowV2` records. They retain path, handler, raw selector/kind,
normalized default mode, obligations and zero-based family inventory order.
No composite key splitting participates in declaration identity. This covers only
the logical `@advice` family; MIR/named forms require their separate audited owner.

`reset_module(path)` establishes a pending parser path and removes only exact-path
rows. Only a trusted successful fresh full-parse owner may call
`aspect_registry_seal_parser_inventory_v2(path, parse_succeeded)` after checking
source generation and parser diagnostics. Reset/absence alone never proves empty.
Failures and per-path overflow are sticky until that path's next parser reset;
global overflow remains incomplete until the existing whole-owner reset.
The parent phase2 capture owns sealing, immutable source/cfg binding and promotion.

Admission limits are 256 rows/256KiB per path, 4096 rows/4MiB globally and 1024
tracked paths, checked before append. Overflows retain partial rows for inspection
but never return complete. Effective legacy maps keep their old behavior.

New containers, statuses, current path and counters join the existing owner
snapshot/restore/reset and transient-promotion functions. BuildSession/source
replay already uses those owners; no competing lifecycle is introduced. A replay
parse is isolated by the existing snapshot/reset/restore owner and cannot replace
retained declaration facts. Typed inventory alone does not authenticate source.

The specs cover pending/known-empty distinction, multiplicity/order, effective
replay isolation, delimiter-bearing exact paths, sticky parse failure, row/byte
limits including global overflow/path bookkeeping, owner restore and actual parser emission. All remain unexecuted; parent
integration and native qualification are still required.
