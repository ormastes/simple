# rt_ Mapping and Pointer Contract Design

Condensed from the 2026-10-31 owner design. Proposed types and syntax are not current Simple.

- The `.spl` extern is the Simple-visible contract. SDN declares target and provider bindings.
- One binding graph carries separate verdicts: mapping, signature, pointer, enforcement, compile, link, load.
- Existing in tree does not mean selected, linked or callable. Each engine has its own evidence row.
- C `T*` is UNKNOWN, not NULLABLE. `_Nonnull` is DECLARED_NONNULL. Only a checked bridge or an artifact-bound trusted contract is ENFORCED_NONNULL.
- Check returns, parameters, callbacks, out params and fields, one nullability value per pointer level.
- Warnings never let an unchecked null reach safe `&T`: a guard is present, or it is an error.
- Implicit raw-to-optional and `&T`/`Option<&T>`-to-bare-`T*` crossings warn, then become errors. Explicit adapters stay legal.
- Evidence: MAPPING on all declared profiles, without compiling them. COMPILE, LINK and LOAD need real artifacts. UNKNOWN, UNTESTED and STALE never count as PASS.
- Diagnostics: SRT001-SRT010 and SNULL001-SNULL008. Baselines are shrink-only.
- Never change a `.spl` return type because of lint status. The contract comes first, and call sites move with it.
