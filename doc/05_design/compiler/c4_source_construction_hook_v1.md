# C4 SOURCE construction hook inventory

Inventory baseline: `release_phase3` merge
`005197db5713d236c52ea26c277db1cb077b89dd` (C4 account/provider foundation).
This is a current-owner inventory and integration plan, not evidence of hook
coverage, physical ownership, runtime execution or a complete SOURCE route.

The selected Path B shared-construction authority is retained in
[the foundation provenance](c4_account_provider_foundation_v1.md). Construction
must publish scalar events before added rich capture/copies. Calling ordinary
`lower_module` and wrapping its returned graph is not the selected route.

## Current construction and replacement owners

Line references identify the baseline, before integration edits.

| Owner | Actual current site | Required opted-path disposition |
|---|---|---|
| MIR builder module allocation | `mir_data.spl:156` / `MirBuilder.new` | Owner/account must precede additional C4 growth. Ordinary nil capture creates no capture tables. |
| MIR function constructor | `mir_data.spl:182` / `begin_function` | Capture actual symbol, name, structural signature and original span before rich construction; reserve before text or child growth. |
| Function finish and fallback | `mir_data.spl:275` / `end_function` | Finalize actual block/local rows; no rich function crosses the new entry boundary. Empty sentinel cannot authorize source success. |
| Module function insertion | `mir_data.spl:328` / `add_function` | Publish matching actual function cursor/revision, or fail opted owner. |
| Local create/rename/retype | `mir_data.spl:338,382,404` | Preserve stable identity, type/name changes, short-borrow metadata and any separate source-symbol binding. Current `MirLocal` has no historical `source_symbol_v1` field. |
| Block create and switch | `mir_data.spl:432,446` | Bind actual dense BlockId; reserve prefix storage before growth; completed block replacement must revise the same row. |
| Instruction flush/replacement | `mir_data.spl:452` / `finalize_block` | Publication replaces the current block sequence. Repeated empty flush leaves completed instructions intact. Counts alone do not prove event fidelity. |
| Raw instruction append | `mir_data.spl:494` / `emit` | Consume one prepared instruction event with exact ordered operands and type; unpaired publication fails. |
| Entry allocation bypass | `mir_data.spl:666` / `emit_entry_alloc` | Direct `blocks[0].instructions` replacement bypasses `emit` outside entry block. Capture this actual replacement or fail the opted path before growth. |
| Terminator publication | `mir_data.spl:849` / `set_terminator` | Flush pending instructions, then consume exact prepared terminator and outgoing ordinal events; overwrite requires row revision. |
| Current owned-raw allocation | `mir_data.spl:635` / `emit_typed_storage_alloc_owned_raw_v1` | Preserve current type/storage allocation provenance checks. These are not a receipt for arbitrary boxed compiler graphs. |
| Module construction core | `_MirLowering/module_lowering.spl:2453` | Factor before rich return. Preserve all existing providers/archive/trait behavior or refuse unsupported opted cases before added capture. |
| Module reset | `_MirLowering/module_lowering.spl:2772` | Existing per-module rich reset is baseline behavior. Install invocation owner before capture begins; no state leaks between modules. |
| Bootstrap publication | `_MirLowering/module_lowering.spl:2903` | Separate bootstrap/flat function branch must publish matching events or fail opted invocation; do not infer coverage from normal function path. |
| Archive grafting | `_MirLowering/module_lowering.spl:3189` | Rich functions/types/constants/statics copied from archive primary globals require original provenance and actual capture authority; no retroactive charging. |
| Early module return | `_MirLowering/module_lowering.spl:3291` | Verification-capture failure currently returns rich module. New opted path must retain scalar failure and cannot expose or seal an incomplete graph. |
| Module final publications | `_MirLowering/module_lowering.spl:3298-3301` | Native-trait thunks, external layout traces and short-call maps mutate output before final rich return. Every opted mutation needs matching row revisions or refusal. |
| Normal function insertion | `_MirLowering/module_lowering.spl:3389-3405` | Actual lower-function result is further VHDL-modified before dictionary replacement. Capture cannot stop at builder finish. |
| Function metadata after finish | `_MirLowering/function_lowering.spl:884-934` | Verification contracts, resolved attributes, GPU, export, driver and VHDL fields change after `end_function`; capture at actual constructor operands and retain authoritative revisions. |
| Short-call finalizer | `_MirLowering/short_call_contracts.spl:14-66` | Actual checked module-local effect rows assign `nogc_strict`/`short_call_contracts` to every function; planner-neutral defaults cannot replace source admission. |
| Static/runtime initialization | `_MirLowering/module_lowering.spl:3435,3560-3703` and `_MirLowering/function_lowering.spl:1079` | Static/constant insertion and generated initialization functions need their own publication events. Preserve ordinary behavior. |

## Current function field classification

The current 36-field function inventory must be captured or explicitly classified
by its actual semantic admission consumer. Symbol/name/signature/locals/blocks/
entry/span require scalar identity and structural children. Generic parameters,
template flag, specialization and bindings require authoritative resolved type
identity. Layout, GPU, C export, driver/VHDL, fast math, FPGA, asm and SIMD metadata
require exact flags/presence and admission-relevant children. Verification
contracts and enum matches require original ordered predicate/binding evidence.
The new no-GC and short-call map fields require actual checked local declaration
provenance. Nonsemantic fields may be omitted only under an explicit consumer
classification; unknown fields do not default to admissible.

## Reuse candidates and known open boundaries

Packet root B is the immutable root retained by the foundation provenance.
`B/source-builder-component-v2` has scoped source review GO for four images and
19 authored UNRUN actual-builder scenarios. It provides scalar builder bookkeeping
and nil-default builder hooks, including terminal sentinel-credit refusal. It
does not establish matching HIR/type/operand cursors, parent first-error short
circuit, source function metadata/declarations or physical copy qualification.

`B/source-view-parent-progress-v1` is explicitly incomplete progress, not SOURCE
GO. `B/source-producer-component/revision2` is the older 23-file logical semantic
producer, not complete scalar SOURCE construction. The HIR admission integration
also reports incomplete work and nine fail-fast helper bodies. None may be
wholesale restored over current compiler owners or presented as passing coverage.

The native type/scope transfer descriptor and original graph storage provenance
must be authentic and hash-bound before physical accounting can be claimed.
Existing ordinary rich constructors and logical cell counters do not supply this
authority. An independent builder-event prerequisite can be integrated while
retaining this exact physical blocker, provided actual unsupported mutations fail
the opted owner and ordinary APIs remain unchanged.

## Integrated builder prerequisite, pending current source review

The scoped implementation owns `mir_data.spl`, the new
`loop_builder_capture_v1.spl`, `loop_view_builder_capture_v1_spec.spl` and its
authored manual mirror, plus this inventory. Production files are frozen for
Astra review before commit; no parent lowerer or generated visitor is changed.

Builder revision 2 manifest SHA-256 is
`4ac8d2dbd2eb469846c3e9f73c9b58329e2e6c5c42883db1bb1ac9710759aeab`;
its original independent scoped review is
`d0875f7e96bfae2c376da123133a7ae1b00ca282d184125ba623975d89b4688b`.
Original reviewed image hashes are:

| Original image | SHA-256 |
|---|---|
| `mir_data.spl` | `2e62f206dcb5781ab5fdaefc678446cb4d10bd0cca31a8f507f1fdf5539005c3` |
| `loop_builder_capture_v1.spl` | `49185082b1acada8e834d8867fdf7fd4df9dcb86b949786eecd82e070e06b0af` |
| `loop_view_builder_capture_v1_spec.spl` | `72594342689774590ede02faedc3a903c0aebe436cb8c2480c21d9e4dcab9b75` |
| `loop_view_builder_capture_v1_spec.md` | `960c0ebab586b9d5115c27ef4719489b73661083cb50b847c18b0f389da32d8d` |

The historical tracked patch was applied three-way, then its revision 2 actual
Span.length and exhausted terminal-credit corrections were retained. The current
builder base differs from that old patch base by only 13 lines: three short-borrow
fields preserved at rename/retype, and the typed nil destination for void calls.
Those current fixes remain. The removed rich `source_symbol_v1` field is not
restored; source binding stays in the scalar capture table. The capture leaf is
byte-identical to the reviewed image. Defaulted cursor arguments retain ordinary
call syntax; nil capture follows the ordinary rich-return route.

The existing `mir_data.spl` grows from 1,644 to 3,028 lines in this bounded reuse.
Astra reviewed preserving that legacy rich owner here: extracting operations
through new rich-argument helpers could change the copy DAG and bootstrap
ownership. A later scalar-only split is deferred until its transfer contract and
runtime evidence can be checked; this prerequisite introduces no such wrappers.

The 19 original actual-builder scenarios are adapted only where they referenced
the removed rich field. A twentieth scenario exercises actual ordinary rename/
retype and checks all three current short-borrow fields with boundary 83, name and
type. None exercises an authenticated parsed SOURCE entry. All 20 remain UNRUN.
The manual stays authored/UNRUN. No interpreter loading result, external model,
new runner or Rust seed substitutes for actual compiled scenario execution.

Qualification must use the admitted canonical compiled SSpec runner and retain
producer hash/source/stage, runtime/provider/backend, isolated cache/output and
the actual 20 registered/executed cases. Then run canonical docgen/maintenance and
the compiler/library/MCP/LSP plus core/MCP smoke requirements once. No suitable
general runner is established for this lane, so these gates are TEST_BLOCKED.
The 512/544 sentinel/capture envelopes are retained logical copy reservations;
they certify neither physical allocation capacity nor authentic source ownership.

The current empty sentinel has a fixed nested field inventory: MirFunction 36,
SymbolId 1, MirSignature 6, Unit MirType 1, BlockId 1, Span 6,
DriverManifestAttr 6, VhdlHardwareMetadata 6 and VhdlClockedMetadata 8: 71
logical fields. All its text, array and dictionary payloads are empty. The fixed
container fields are included in that count; object headers and allocator
capacity are outside this logical model. One construction plus the selected two
return/assignment copies totals 213 fixed field slots, within the retained
512-slot conservative envelope. The current layout adds one field per copy
compared with the historical layout, without changing the selected limit or
making any native copy/size claim.

The concrete authenticated-entry blocker is
`FUNCTION-TYPE-PUBLICATION-01`, retained in
`B/source-function-type-publication-component/revision2-design-boundary.json`.
The synthetic driver planner needs a producer-issued scalar HIR root at original
storage before any additional rich HirFunction/body transfer, with bounded actual
scope/name/type reads. The current packets do not establish that capability or
the full HIR body readset. Fixed entry charges, source-span lengths, node counts,
blanket manifest rejection or caller-supplied descriptor IDs are not substitutes.

No SOURCE success entrypoint is declared implemented. Actual source metadata,
declaration/provider authority and all external builder mutations remain parent
integration obligations. Runtime, docgen, native ownership/copy, RSS and complete
SOURCE→PLAN→EMIT acceptance remain UNRUN.

Static integration results on 2026-10-25: working/staged direct-env guards PASS,
staged whitespace validation clean, zero executable specs under `doc/06_spec`,
20 authored scenarios and the capture leaf's exact original hash confirmed.
The scoped new-leaf/spec placeholder scan found no placeholder passes. Astra's
current integration SOURCE/API/ORACLE review found no remaining P0/P1. These
results establish source hygiene only; behavioral verification is TEST_BLOCKED.
