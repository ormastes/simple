# Pure Simple foreign parameter symbol identity

Status: permanent source repair proposed; actual-owner Phase1 RED/GREEN PASS;
rebuilt native producer, imported product behavior and performance UNRUN.
Authoritative bug DB reconciliation and actual fix commit binding pending.

The pure f2 producer f2ce31b4e4dea1ea6ca3e8726cd411144914c24ffcf58722021f38c4b6393dec
reported four unrelated Close trait conversions for real imported
DuplicationConfig parameters. Retained source snapshot
bb003c6170066d540d65b094f580c00dcdcb849079101212c35b133c3bacda7a
stores provider-local HirType.Named SymbolIds in a process-global bare-name
parameter registry, then consumers interpret them in their own SymbolTable.
The exact numeric IDs from that native failure have not been independently
decoded; the ownership defect is established in source and an independent
real-owner colliding-SymbolTable criterion, not by claiming a replayed native
product fix.

Repair parameter insertion and lookup using the existing recursive symbol-free
metadata policy. Keep global-first primitive ABI priority: an imported local
Function signature can be erased all-i64, so preferring it unconditionally
regresses mixed i32/i64 calling conventions. Reject foreign symbol-bearing
registry entries and retain the existing consumer-local signature fallback.
Keep rejected parameter names separate from valid scalar return hints and
promote the rejection map with the other cross-module registry roots.

Actual qualification: private d958 Phase1 interpreter executed eight cases on
the full production owner. Baseline3PASS/5FAIL; candidate8PASS/0FAIL. Native
image, source confinement, input hashes and closed Jobs were verified. The
tested registry function bodies and unchanged resolver match the local
proposal exactly; the coherent frozen full source closure has additional
unrelated features and is not presented as a local full-suite qualification.

Evidence: build/native_probe/imported-type-identity-20261012-astra/v2/QUALIFICATION.md.
Durable regression: test/01_unit/compiler/mir/imported_parameter_identity_spec.spl
(proposed, not yet installed). Covers recursive nominal metadata, dynamic
traits, inference, rejection lifetime and return hint preservation, real
numeric-ID collisions, mixed-width ABI, and ambiguous global names.

EasyFix array-element field0 substitution is a separate observed native bug;
this registry patch does not establish its repair. Native artifact promotion
requires a rebuilt producer, affected-entry cache invalidation, semantic
positive/negative checks, and performance/RSS qualification. No global trait
disable, arbitrary integer fallback, or shared numeric ID space is introduced.
