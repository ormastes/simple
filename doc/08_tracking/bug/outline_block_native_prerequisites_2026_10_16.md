# Outline native block prerequisites — 2026-10-16

Status: source repairs in progress; native cycle 2 UNRUN; database reconciliation pending.

The genuine 0CD6 native producer compiling frozen 8642b544daf854e3254bd3c3aaaea36a3f16b0f3 processed 96 MIR modules:88 succeeded,8 failed,54 fatal diagnostics. No SPL objects, link or executable resulted. Failure receipts retain full stderr, exact per-module ledger and hashes under the session-owned outline-receiver-native-cycle1/terminal-failure-analysis evidence directory. This is not Phase3/compiler admission.

## Missing native trait defaults

BlockDefinition has17 slots. The baked producer emits an empty method placeholder without its signature when an implementation omits a default, then truthfully rejects unequal table/signature lengths. Three math builtins contain11 methods, Shell8, Markdown6, SQL9, Regex9 and JSON7. Compatibility adapters explicitly implement each genuinely missing slot using canonical trait behavior. Existing real overrides remain authoritative. The table-length checks are unchanged; arbitrary user implementations omitting defaults are not fixed by this source compatibility repair. Immediate workaround comments carry recover=8642b544daf854e3254bd3c3aaaea36a3f16b0f3.

## Block policy stubs and ownership

The preexisting h_skip_policy and h_treesitter_outline returned hardcoded OutlineRequired/opaque-empty instead of calling the actual handler. The actual optional trait value must be unboxed before dispatch. Tests require custom handler policy and outline metadata in all three fast-mode policies and normal mode. The default registry passed its mutable local through a plain free function; the owner itself documents value-copy loss in register_block. Use actual local mutable receiver calls. Reset replaces the authoritative global value with a fresh default registry; previously returned values remain snapshots. No alias-wide clear behavior is claimed.

## Full Unicode classification, unchanged byte spans

Missing native text methods are replaced with nonempty/all-scalar predicates for complete Unicode17 Alphabetic, Numeric(Nd|Nl|No) and White_Space; digits retain the existing ASCII-only oracle contract. Invalid UTF8 fragments fail closed. Existing full Alphabetic tables are reused. Numeric and White_Space data are pinned to unicode-org/unicodetools commit ecd26be2e82be37609090942c14e518e57e905d8, tag final-17.0-20250910, paths unicodetools/data/ucd/dev/{UnicodeData.txt,PropList.txt}. The release-tag PropList header says17.0.0.

UnicodeData SHA256:2e1efc1dcb59c575eedf5ccae60f95229f706ee6d031835247d843c11d96470c. PropList SHA256:130dcddcaadaf071008bdfce1e7743e04fdfbc910886f017d9f9ac931d8c64dd. Numeric1924 scalars/146 ranges; White_Space25 scalars. Unicode License v3 applies; existing license lives at examples/05_stdlib/spipe/tools/unicode/UNICODE-LICENSE.txt. Pure-Simple generator source is supplied; its execution remains UNRUN. Research-only exhaustive comparison of emitted range sets against all official property members passed; this does not execute Simple or qualify native predicates.

Concrete pending tokenizer limitation: payload[i] lowers to one-byte text while text.len and spans are byte-based. Whole valid multibyte text is classified correctly by the helper contract, but those existing scanners still pass individual bytes. This repair preserves all index/span units and does not claim Unicode tokenization. Historical Rust classification uses its bundled Unicode version; exact cross-version identity is not claimed.

## Typed JSON replaces passthrough stubs

The previous parse_json returned Ok(raw text), incompatible with compiler JsonValue(kind:JsonKind); json_to_const stringified the raw text. The genuine typed std.common.json.value parser now supplies an exhaustive nominal adapter preserving nested arrays/objects, errors and object-key behavior. Its integer number representation widens to compiler JsonKind.Number(f64). Constant conversion preserves scalar/array kinds. Objects have no ConstValue representation and return nil, propagated through enclosing arrays; full objects remain present in BlockValue.Json. This uses the existing optional evaluation contract, not a new object representation.

## Qualified patterns

The13 top-level patterns incorrectly named constructor helpers as enum variants; actual TopLevelItem variants are used instead. Existing helper constructor calls remain intact. TokenKind cases at the failed matches are qualified without a permissive fallback. The baked producer's bare-pattern inference failure is a compiler issue; this is a bounded explicit-qualification workaround.

## Validation limits

Source controls exercise the actual parser, custom trait handlers, builtin registry, byte spans, full Unicode strings and typed JSON. All native execution of this revision remains UNRUN pending root source review and a genuine cache-preserving cycle2. Only two native attempts remain in the original three-cycle budget; no budget reset, stubs, seed fallback, smaller-context object graft or unsafe link qualification is allowed.

## Bounded desugared builtin presence repairs

The actual declarations require explicit bool/text pairs:2 BlockOutlineInfo constructors,18 BlockExample constructors and6 SQL Completion constructors. Absent values now carry false/emptytext; existing Some literals carry true/exactpayload. All other code, descriptions, order and kinds remain unchanged. Actual-handler controls inspect math/opaque outline metadata, all builtin example absence fields and SQL present/absent completion fields including snippet placeholders. These source controls remain nativeUNRUN.
