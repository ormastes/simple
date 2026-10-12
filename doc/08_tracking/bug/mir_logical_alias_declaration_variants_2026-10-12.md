# MIR declarations need logical variants of a physical HIR owner

Status: source repair in progress; new native controls UNRUN. No production activation or RSS qualification.

The retained monomorphizer accepts two logical dictionary keys referencing the same complete physical HIR module. `collect_generics` retains the last logical template registration. `process_modules` publishes specialization function dictionaries only on that owner, while aliases share the actual SymbolTable/counter. Final archive keys bind logical identity and coverage, and complete final bodies can therefore differ legitimately.

The first archive MIR declaration repository keyed every summary by decoded `HirModule.name`; its borrowed lowerer required that one summary's full body digest. This cannot represent both legitimate variants. Rejecting a different final digest or reusing one summary by spelling would change retained alias semantics.

The private repair keeps a typed logical source binding on each summary, separate from physical HIR name/path and actual symbol ownership. It includes the actual admitted canonical physical path, full source SHA256/bytes and original archive key. The driver must compare this data against its genuine issued final inventory. The binding itself grants no admission. Logical summaries retain their own complete final body/default-expression pins; the borrowed consumer selects an explicit logical key and still checks the exact full body.

Complete-function identity has one lower HIR owner, extracted unchanged from the existing mono function-record implementation, with its original generated codec and domain. MIR declaration projections retain that actual full digest. Declaration seals now include the source binding and function digest under v2 domains. Legacy single-owner mechanical callers keep their existing constructors and default key.

Callable/default/global alias equality requires the admitted same-physical-source tuple and the complete retained declaration contract. Comparison copies omit only final archive/body transport pins; they retain expression content digests, selectors, types, effects, linkage/visibility/mutability and spans. Original artifacts stay fully pinned and are never replaced by comparison projections. Distinct declarations retain conflict diagnostics. Mono's actual logical table-owner binding can reference the existing physical emission name only through the typed source binding; SymbolTable ownership is preserved.

The existing callable prescan is extracted without changing ordinary prescan order. This lets the driver retain actual layout-firstwinner order while covering specialization signatures/defaults on other logical variants.

`test/fixtures/compiler/mir_logical_declaration_variants` uses the genuine final-repository setup and actual generic provider, requiring its source root. Its eleven numbered controls exercise actual final capture, both distinct complete variants, wrong-body refusal and exact logical-key lowering, source conflict and unsealed key substitution. All are UNRUN; they are not replaced by struct-field-only or forged-admission tests.

Remaining production work: actual private production try-getter dispatch; complete bounded MIR loop with existing diagnostics/ICE/counter policies; normal physical emission of e3-proven specialization-only-later functions while preserving firstwinner ordinary bodies/global initializers/counters; all retained logical/cold receipt rows; owned metadata/default registry publication and actual native acceptance. Full later-alias lowering followed by dropping duplicate output would double counters and is not the intended solution. No synthetic partial HirModule or name-only union is authorized.
