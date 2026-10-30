# TLDR: return-type interface (RTI) (2026-10-27)

Full design: `return_type_interface_design.md`. Base `origin/release/1.0.0` @ `b098b5ed8bd`.

- One lookup for the declared return type of EVERY callable (fn, method, static, trait method incl. default body, generic template, re-export/alias): `callee_return(expr, symbols, receiver_type)` in `src/compiler/20.hir/return_type_interface_v1.spl`.
- Identity = `DeclRef(module_id, decl_id)` ("fn:pick", "struct:Box::open", "trait:Maker::make"); never a per-module `SymbolId`. DeclRef equality IS type identity (replaces name/module-spelling folding in `enum_payload_named_alias_equal`).
- Entry is exactly one of three: `Decided(term)` (resolved; `Param(i)` only on a generic template row), `Union([terms])` (closed set: `@cfg` arms / enum family), `AsyncRef(DeclRef)` (lazy set-once pointer, single-flight fill from the callee's TLDR). Never `Any`/`Infer`/`nil`. Consumers match all three; an unfilled `AsyncRef` or a `Param` at MIR is a hard error.
- Terms are symbol-free and HIR-shaped (`Builtin | Nominal(DeclRef,args) | Result | Optional | Array | Dict | Tuple | Function | DynTrait | Param(i)`); `bind(term, symbols)` turns one into the consumer's local `HirType`, `decl_ref_of(symbols, id)` goes the other way.
- Export: TLDR companion section `rti` (`rti|decl_id|arity|decided|...` / `union` / `async`), rows canonical + sorted, digested under `simple/interface/rti/v1` into the module `iface_digest` — one cold invalidation, then body-only edits stay cached.
- Fail closed: E-RTI-001 no row, 002 AsyncRef unfilled at MIR, 003 Param at MIR, 004 unbindable DeclRef, 005 alias cycle, 006 two rows one key, 007 Any/Infer/Error at export — each names callee, module and interface digest.
- Replaces (then deletes): `module_fn_declared_returns` (#4754, `mir_lowering_types.spl:710`), name-keyed `_bootstrap_fn_ret_hir_types` (`mir_data.spl:2487`), `mir_trait_method_ret_key_v1` (#4998), spelling fold in `enum_payload_type_identity.spl:18`.
- PRs: PR1 API + table + fn/method rows + MIR `enum_match_expr_type` consumer + 3-module fixture spec; PR2 trait/dyn/impl rows (delete #4998 key); PR3 TLDR section + digest + reader single-flight fill; PR4 generics `instantiate` + alias `AsyncRef` rows (delete M1/M2); PR5 payload identity + HIR typing on DeclRef, strict default.

```sdn
graph:
  nodes:
    - {id: hir,   label: "HIR module (target-neutral)"}
    - {id: rows,  label: "rti rows: DeclRef + Decided|Union|AsyncRef"}
    - {id: tldr,  label: "TLDR `rti` section -> iface_digest"}
    - {id: table, label: "shared set-once table (single-flight)"}
    - {id: use,   label: "HIR typing + MIR (bare Ok/Err, payload, match subject)"}
  edges:
    - {from: hir,   to: rows}
    - {from: rows,  to: tldr}
    - {from: tldr,  to: table, label: "AsyncRef fill"}
    - {from: rows,  to: table, label: "in-process (PR1)"}
    - {from: table, to: use,   label: "callee_return / bind; miss = E-RTI fatal"}
```
