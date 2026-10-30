# HM-owned typed tree producer: authored manual

Source: `test/01_unit/compiler/types/hm_owned_typed_module_v1_spec.spl`.
Status: authored expected behavior; no runtime tests or docgen ran.

1. Parse and lower an actual function returning literal 42. Actual module inference, synthesis/check and substitution resolution must produce an i64-annotated clone while original nodes stay unannotated.
2. Produce bool annotations from actual true. Repeat inference and mutate only the returned symbol dictionary; the original and second result must retain independent containers and original nodes remain unchanged.
3. Parse-valid i64 returning true must yield actual inference rejection with no partial typed clone or original annotation mutation.
4. Unsupported arithmetic/profile nodes, oversized metadata and insufficient aggregate work/node/function limits must refuse before inference.

Typed HIR is compiler data. It grants no source provenance, semantic completeness, live issuer installation, compiled execution or cache admission.
