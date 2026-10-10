# Imported generic composite field owner scope

Status: OPEN; draft repair and regression fixture AUTHORED_UNEXECUTED.

Observed Phase 4 Caret suite producer 4cca9585 emits unresolved Op/Cpl diagnostics for imported SimpleRing<Op,Cpl>. Source inspection confirms ModuleSurfaceComposite retains parameters, but imported field dependency registration and projection did not bind them. Local prescan_composite_field_types already provides a saved/restored binder scope.

Draft repair filters declared owner parameters from transitive dependency materialization, installs a lexical Class scope for field projection, preserves TypeParam names/bounds through the existing prescan parameter map, and restores consumer state. Both scalar and nested imported projections prefer active owner binders over qualified same-spelled module declarations. Non-generic dependencies remain materialized in the existing consumer scope.

Regression: test/fixtures/native/imported_generic_owner_scope/{owner,main}.spl covers imported generic class/struct fields, optional and array containers, nested generic Packet<Op>, and same-spelled owner/consumer decoys. Existing imported_generic_fields is the non-generic dependency control. Main returning zero is not semantic execution evidence. Admission requires actual HIR field-map checks, concrete specialization and executed field reads, plus normal compiler/core/MCP verification. No producer rebuild or PASS claimed yet.

Related but distinct: explicit call type arguments are discarded in the parser; inferred optional generic results can produce Some(nil). This field-scope draft does not claim to fix those call-transport defects.

Astra source review accepted saved/restored owner scope, dependency filtering and binder-first projection; review identified optional has_X sugar and exact has_-prefixed binder preservation, now included. Review does not establish executable qualification.
