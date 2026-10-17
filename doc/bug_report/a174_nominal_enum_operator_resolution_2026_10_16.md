# A174 nominal enum operator resolution (2026-10-16)

Status: pending bug database admission; workaround and regression UNEXECUTED.

Retained producer: pure-Simple A174 SHA256 a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994, Windows LLVM23.1.3/MSVC. Authority final attempt3 reported enum operands as struct compiler.driver.smf.package_image_v1.PackageSectionKindV1 and failed operator-overload lookup at original package_image_v1.spl127 (==) and runtime_std_package_membership_v1.spl261 (!=). Evidence: external phase3-validation-20261016/authority-attempt3-failure-table.md. This proves those diagnostics, not the internal resolver/metadata root cause.

Workaround reuses existing package_section_kind_name_v1: its exhaustive ten-variant mapping is injective. Compare canonical names with the original equality/inequality operators; no casts, wildcard, numeric tags or representation changes. The analogous lookup comparison at original package_image_v1.spl91 is changed consistently but has no retained attributed failure. Preserve lookup first-match behavior, required-section multiplicity checks and membership validation/error ordering.

Original source reference:6569adf5762d5292650323c0cc92a19c6d3779f2 at those three sites. This is not a compiler-owner repair commit and authorizes no automatic checkout/removal. Actual owner recovery commit remains unknown; optional recover tokens are omitted. Remove workaround only after a rebuilt producer correctly handles nominal enum equality in these positive/negative cases.

The authored regression enumerates all ten declared variants and checks equality and inequality for all100 ordered pairs against independently known distinct list positions. It is UNEXECUTED and does not establish A174 match/enum hydration or full compiler acceptance. No fourth authority build is permitted. The26 HirType.named diagnostics and pathless enum constructor payload mismatches remain unresolved separate evidence; this patch does not claim to fix them.

Implementation candidate: 6ccaf88558fd2190de47e72861bd5779d5bb003c (source identity only, UNEXECUTED).
