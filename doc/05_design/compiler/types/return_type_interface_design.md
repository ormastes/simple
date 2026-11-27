# Return-type interface (RTI) — one declared-return lookup for every callable

Status: DESIGN (2026-10-27). Base `origin/release/1.0.0` @ `b098b5ed8bd`.
TLDR: `return_type_interface_design_tldr.md`. Owner lanes: true-per-file lead
(TLDR interfaces), cache lane lead (interface digest).

## 1. Problem — the current mechanisms and why they keep breaking

Cross-module "what does this callee return?" is answered today by four
independent, differently-keyed tables, each added for one incident:

| # | Mechanism | Code (file:line) | Key | Covers | Does NOT cover |
|---|---|---|---|---|---|
| M1 | `module_fn_declared_returns` (#4754) | `50.mir/mir_lowering_types.spl:710`; filled `50.mir/_MirLowering/module_lowering.spl:2591-2595`; read `50.mir/_MirLoweringExpr/switch_operators_calls.spl:2633-2634` | module-LOCAL `symbol.id` | plain `Call` whose callee is `Var`/`NamedVar`, same module | methods, trait methods, imported callees (id is per-table), aliases |
| M2 | name-keyed `_bootstrap_fn_ret_hir_types` registry | `50.mir/mir_data.spl:2487-2520`; read `switch_operators_calls.spl:2180,2223` | bare / qualified NAME | flat closure prescan | duplicates go `ambiguous -> nil` (silent); symbol-bearing returns refused (`hir_type_metadata_symbol_free`) |
| M3 | trait-method key `mir_trait_method_ret_key_v1` (#4998, `7071d9975bf`) | `50.mir/_MirLowering/declaration_providers_v1.spl` (`trait-ret:{module}.{Trait}::{method}`), read in `enum_match_expr_type` | normalised module+trait+method TEXT, stored in M2 | imported trait receiver, symbol-free returns | struct/enum-returning methods (M2 refuses them), default-body methods not re-registered per impl, re-exported traits (module spelling differs) |
| M4 | `enum_payload_named_alias_equal` | `50.mir/_MirLoweringExpr/enum_payload_type_identity.spl:18-38` | kind + name + folded `defining_module` | same enum under two local ids | compares SPELLINGS, not identities; depends on `mir_layout_canonical_module_name` folding path vs dotted names |

Symptoms (all one root cause — no stable cross-module type identity, no
single owner of "declared return"):
`enum match: bare variant 'Ok' is ambiguous ... type_hint "known non-enum type"`
(`switch_operators_calls.spl:2887,4207`); enum payload mismatches when the same
type appears under different symbol ids per module; `E-MIR-TYPE-TypeParam:
unsubstituted generic 'T' reached MIR` (`50.mir/_MirLowering/function_lowering.spl:1455`)
when a generic callee's declared return is consulted raw.

Existing identity encoders already compute the right thing but are not shared:
`20.hir/abi_interface.spl:32-39` (`symbol_identity` = module + name),
`40.mono/nominal_type_identity.spl:7-17` (`named(owner,name)` key),
`20.hir/nominal_type_relocation.spl` (relocates Named ids table-to-table).
The TLDR function header (`20.hir/archive/tldr_function_header_v1.spl:59-90`)
exports returns as TEXT names and supports only `i*/u*/f*/bool/void` — every
nominal return is `body-required`.

## 2. Design rules (from the user's architecture rules)

1. Imports come from per-module TLDR interface summaries (forward declarations).
   A cross-module reference is a lazy `(module_id, decl_id)` pointer, filled
   once via single-flight (`src_based_tldr_build_v1.md` §7).
2. HIR is target-neutral; MIR picks the target. A `@cfg`-dependent return is
   therefore a closed UNION of arms in the interface, never pre-selected.
3. No `Any` outside `unsafe`, `nil` only in `unsafe`: an interface entry is
   never an untyped placeholder.
4. Fail closed with a diagnostic naming the callee, its module and the
   interface digest it was read from. Never guess, never "ambiguous -> nil".

## 3. Identities

```
DeclRef   = { module_id: text, decl_id: text, display: text }   # stable, never a SymbolTable id
module_id = canonical dotted logical module name (module_logical_name_from_path;
            the same fold mir_layout_canonical_module_name performs today)
decl_id   = stable_symbol_id(SymbolComponents(package, module_id, item_kind,
            owner_id, name, signature: ""))        # 35.semantics/symbol_id/stable_id.spl:49
            — the SAME content-derived 128-bit id FrozenPublicFactV1.stable_symbol_id
            carries (true-per-file lead, 2026-10-27); pure sha256 over the
            components, so deterministic across processes and targets. The
            signature component is "" by construction: within one module a
            callable is identified by (owner, name) — overloads are E-RTI-006 —
            and a type by (kind, name), which is all an importer knows.
display   = "<kind>:<Name>" | "<owner display>::<method>" | "trait:Maker::make"
            | "impl:<Type>@<Trait>::<method>"    diagnostics only, never identity
```

`DeclRef` equality (module_id, decl_id) IS type identity. `SymbolId` stays
module-local and is only a cache of the binding `DeclRef -> local id` inside
one table.

Interface type term (symbol-free, serialisable, HIR-shaped):

```
RtType = Builtin(name)                       i8..u64 f32 f64 bool char text unit never any
       | Nominal(DeclRef, args: [RtType])    struct/class/enum/trait/alias target
       | Result(ok, err) | Optional(inner) | Array(elem, size?) | Slice | Dict(k, v)
       | Tuple([..]) | Function(params, ret) | DynTrait(DeclRef) | Ref/Ptr/Unique/Shared/Weak(inner)
       | Param(index)                        generic binder, binder-indexed like
                                             generic_tldr_view_v1 (alpha-invariant)
```

`Any` is the builtin term `b:any` and round-trips through the interface.
`Infer` and `Error` are not representable: an exporter that meets one emits an
error row (§7), not a term.

## 4. The tri-state entry (centre of the API)

Every callable row is exactly one of three forms:

| Form | Meaning | Who may consume it |
|---|---|---|
| `Decided(term)` | fully resolved term; contains `Param(i)` only when the callable itself is a generic template (arity recorded on the row) | everyone; MIR additionally requires `rti_concrete` (no `Param`) |
| `Union([term..])` | closed set of decided alternatives: `@cfg` arms of a target-dependent return, or an enum/Result family a consumer tests variant-by-variant | HIR typing tests membership; MIR selects the arm for its target or fails closed |
| `AsyncRef(DeclRef)` | lazy set-once pointer to another row (re-export, alias, `impl` delegation, not-yet-loaded callee TLDR); filled once via single-flight through the reader | HIR typing may defer; **at MIR lowering an unfilled `AsyncRef` is a hard error (E-RTI-002)** |

Consumers match all three explicitly — there is no `_` arm and no `nil`.

## 5. Lookup API (one module: `src/compiler/20.hir/return_type_interface_v1.spl`)

```
struct CalleeKey:   owner: DeclRef?   name: text   is_static: bool
enum ReturnTypeEntry: Decided(RtType) | Union([RtType]) | AsyncRef(DeclRef)
struct ReturnTypeRow: decl: DeclRef  key: CalleeKey  type_param_count: i64  entry: ReturnTypeEntry

class ReturnTypeInterfaceTable:          # shared, immutable rows, set-once fill
    rows_by_module: Dict<text, Dict<text, ReturnTypeRow>>   # module_id -> decl_id -> row
    fn lookup(key: CalleeKey) -> Result<ReturnTypeRow, RtiError>
    fn resolve(entry) -> Result<ReturnTypeEntry, RtiError>   # follows AsyncRef chains, cycle-guarded
    fn instantiate(row, args: [RtType]) -> Result<RtType, RtiError>   # substitute Param(i)
    fn bind(term: RtType, symbols: SymbolTable) -> Result<HirType, RtiError>    # DeclRef -> local id
    fn decl_ref_of(symbols: SymbolTable, raw_id: i64) -> Result<DeclRef, RtiError>  # local id -> DeclRef
    fn callee_return(expr: HirExpr, symbols, receiver_type: HirType?) -> Result<ReturnTypeEntry, RtiError>
```

`callee_return` is the single entry point every consumer uses. Resolution:

| Callee expression | Key derivation |
|---|---|
| `f(x)` — `Var`/`NamedVar` | `decl_ref_of(symbol)` -> `(module, fn:f)`; a wildcard-imported name with invalid id -> `module_callables` row -> DeclRef; none -> E-RTI-001 |
| `recv.m(x)`, receiver type `Nominal(T)` | `(T.module, T.decl_id::m)`; if absent, every `impl:T@*::m` row in the importer's closure; two hits -> E-RTI-006 |
| `recv.m(x)`, receiver `DynTrait(Tr)` or a trait-typed param | `(Tr.module, trait:Tr::m)` — default-body methods are rows like any other |
| `T.m(x)` static | same as concrete receiver with `is_static=true` |
| generic `g<..>(x)` / `recv.m<..>()` | row with `type_param_count > 0`; `instantiate(row, args)` where args come from HIR typing (explicit) or mono (inferred); a `Param` left unsubstituted at MIR -> E-RTI-003 |
| re-export `use m.{a as b}; export b`, `type Foo = m.Bar` | exporting module emits `AsyncRef((m, fn:a))` / `AsyncRef((m, enum:Bar))`; `resolve` follows, depth-limited (32, same as generic view), cycle -> E-RTI-005 |

Match subjects, bare `Ok`/`Err`, enum payload checks and `enum_match_expr_type`
all call `callee_return` then `bind`; payload equality becomes DeclRef
equality (`Nominal(a) == Nominal(b)` iff `a.decl == b.decl && args equal`).

## 6. Export: TLDR `rti` section and interface digest

Producer: `80.driver/cache/module_tldr_sections_v1.spl` gains kind `rti`
(beside layout/trait/type/const/impl/generic). One row per callable, canonical
text via `canon_*` (`compiler.common.cache.canonical_identity`):

```
rti|<decl_id>|<type_param_count>|decided|<canon term>
rti|<decl_id>|<type_param_count>|union|<canon seq of terms>
rti|<decl_id>|<type_param_count>|async|<module_id>|<decl_id>
```

Rows are sorted (`canonical_identity_sort_texts`); the row set is one part
list fed to `interface_digest_of` (`80.driver/cache/action_key.spl:184`) under
a new domain tag `simple/interface/rti/v1` (registered under `domains:` in
`80.driver/cache/schema/cache_protocol.sdn` next to `interface`, line ~92;
reseal the `#sdn-crc32` header if present — `push-sdn-crc32-sealed` checks it).
Agreed with the cache lane (2026-10-27): **no new field** on `ActionDep` /
`SmfManifestEntry`; `rti_digest` is folded into the EXISTING `iface_digest`
input as one length-framed tagged component `rti=<len>:<digest>` in a fixed
position after `source_interface_parts`; a module with no callables folds an
explicit empty-set marker, never omits the component. PR3's spec must show:
body-only edit → digest unchanged; declared-return edit → changed; row reorder
→ unchanged. Cache-key impact: one cold invalidation when the fold lands, then
body-only edits stay cached. The textual `source_interface_parts`
under-capture (`action_key.spl:197-213`) is narrowed, not widened. RTI does
not reach `hir_cache_key` (owned by the HIR-cfg lane); if it ever must, that
lane is consulted first. Persisted handles carry a sha256 identity (XXH3 is
index only, #4924); invalidation digests the full summary content.
Consumer: an `rti` section reader registered beside
`20.hir/hir_lowering/_Items/module_tldr_registration.spl` and the
`module_tldr_sections_v1` kinds — the registration API is the contract with
the per-file lead's `readTldr(module_id)` (PR2b, `SIMPLE_TLDR_IMPORTS`), whose
internals RTI never depends on. Terms stay target-neutral (`Union` keeps every
`@cfg` arm). The body route (`tldr_function_header_v1.spl` "body-required")
is retired only where an `rti` row exists; any remaining unsupported case stays
a counted per-module fallback, never silent. In-process, before the reader
lane lands, the same rows are produced from each lowered `HirModule` by
`rti_rows_from_hir_v1(module)` — the prescan providers
(`declaration_providers_v1.spl`) feed them to the table.

## 7. Failure modes (fail closed)

| Code | Condition | Diagnostic (span = call site) |
|---|---|---|
| E-RTI-001 | no row for key | `callee '{name}' of module '{m}' has no return-type row (interface {digest})` |
| E-RTI-002 | `AsyncRef` unfilled at MIR | `return type of '{m}.{decl}' not loaded at MIR lowering; reader fill failed/absent` |
| E-RTI-003 | `Param(i)` reaches MIR | replaces `function_lowering.spl:1455` text with the row's decl and binder |
| E-RTI-004 | `bind` finds no local symbol for a DeclRef | `type '{m}.{decl}' is not imported in '{consumer}'` |
| E-RTI-005 | alias/re-export cycle or depth > 32 | lists the chain |
| E-RTI-006 | two rows for one key (overload across impls) | lists both decl refs — never collapses to nil |
| E-RTI-007 | exporter meets `Infer`/`Error` return or an unbound type parameter | row refused at export; module interface build fails |

`Union` selection at MIR with no arm for the active target is E-RTI-002-class
(hard error naming the target).

## 8. Migration (replace, then delete)

| PR | Content | Deletes |
|---|---|---|
| PR1 | `return_type_interface_v1.spl` (types, table, `lookup/resolve/instantiate/bind/decl_ref_of/callee_return`), `rti_rows_from_hir_v1` for plain functions + struct/class methods (incl. static), MIR `enum_match_expr_type` consults RTI first; 3-module fixture spec red→green | — (old paths stay as fallback; `SIMPLE_RTI_STRICT=1` makes a miss fatal) |
| PR2 | trait methods (declared + default body), `DynTrait`, `impl` rows across modules, E-RTI-006 | M3 (`mir_trait_method_ret_key_v1` + its two prescan loops), the #4998 spec is rewritten on RTI |
| PR3 | TLDR `rti` section export + import, interface digest fold, `AsyncRef` fill via reader single-flight | `body-required|unsupported` for nominal returns in `tldr_function_header_v1.spl` |
| PR4 | generic rows + `instantiate` wired from HIR typing and mono; alias / re-export `AsyncRef` rows | M1 (`module_fn_declared_returns`), M2 (`_bootstrap_fn_ret_hir_types` + `bootstrap_fn_ret_hir_type_*`) |
| PR5 | enum payload identity + match-subject typing + HIR inference of imported callables on DeclRef | M4 folding (`enum_payload_named_alias_equal` becomes DeclRef compare); `SIMPLE_RTI_STRICT` default on, flag removed |

Each PR: red→green spec on the shared fixture
`test/fixtures/compiler/rti/{kinds,reexport,consumer}.spl`, lint on changed
files, explicit `BASE..NEW` for `check-tree-size-push.shs` and
`check-no-conflict-markers-push.shs`, land with `gh pr merge --admin --merge`.

## 9. Diagram

```sdn
graph:
  nodes:
    - {id: src,    label: "module source (A: kinds, B: reexport, C: consumer)"}
    - {id: hir,    label: "HIR lowering (per module, target-neutral)"}
    - {id: rows,   label: "rti_rows_from_hir_v1 -> ReturnTypeRow {DeclRef, tri-state entry}"}
    - {id: tldr,   label: "TLDR companion `rti` section (canonical rows)"}
    - {id: digest, label: "interface_digest_of(simple/interface/rti/v1) -> iface_digest"}
    - {id: table,  label: "ReturnTypeInterfaceTable (shared, set-once, single-flight fill)"}
    - {id: typing, label: "HIR typing: imported callable -> callee_return"}
    - {id: mir,    label: "MIR: enum_match_expr_type / bare Ok-Err / payload identity / match subject"}
    - {id: err,    label: "E-RTI-001..007 fail closed"}
  edges:
    - {from: src,    to: hir}
    - {from: hir,    to: rows}
    - {from: rows,   to: tldr,   label: "export (PR3)"}
    - {from: tldr,   to: digest}
    - {from: tldr,   to: table,  label: "import: AsyncRef fill via reader"}
    - {from: rows,   to: table,  label: "in-process (PR1)"}
    - {from: table,  to: typing, label: "lookup/resolve/instantiate/bind"}
    - {from: table,  to: mir,    label: "callee_return; AsyncRef/Param at MIR = error"}
    - {from: typing, to: err}
    - {from: mir,    to: err}
```

## 10. Fixture shapes the PR1 spec must turn red→green

Module A `kinds`: `enum Shape: Circle(r: f64) | Square(s: f64)`; `pub fn
pick(n: i64) -> Result<Shape, text>`; `struct Box: fn open() -> Result<Shape,
text>`, `static fn make() -> Box`. Module B `reexport`: `use kinds.{pick as
choose, Box}` + `export choose, Box`. Module C `consumer`: `match pick(1)` with
bare `Ok(s)`/`Err(e)` arms (M1 miss when imported); `match Box.make().open()`
(method on concrete receiver — no table today); `match choose(2)` (re-export —
PR1 resolves through B's import binding to A's DeclRef; the `AsyncRef` row form
lands in PR4); payload identity: `Shape` reached through C's table must equal
`Shape` reached through A's table by DeclRef, not by name folding.
