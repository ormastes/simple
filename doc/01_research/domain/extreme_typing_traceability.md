# Domain precedents for the conditional design

Status: bounded research, 2026-11-01. These external precedents support design
choices; they are not evidence that Simple implements or qualifies them.

| Primary source | Useful precedent | Limit |
|---|---|---|
| [Rust API Guidelines: type safety](https://rust-lang.github.io/api-guidelines/type-safety.html) | Distinct newtypes express distinctions the type checker can enforce. | Does not define Simple's visibility, primitive catalog, newunit semantics or assurance policy. |
| [StrictDoc traceability guide](https://strictdoc.readthedocs.io/en/stable/stable/docs/strictdoc_01_user_guide-TRACE.html) | Explicit requirement identifiers, hierarchy and source markers support navigation. | A linked source/test is not qualified execution evidence. |
| [OpenFastTrace repository](https://github.com/itsallcode/openfasttrace) | Import, trace and report workflows provide a useful CLI precedent. | Does not establish Simple snapshot semantics, SDN compatibility or coverage policy. |

The supplied proposals' other UI/tool analogies are inspiration, not verified
equivalence claims. The local design follows repository source ownership first:
common traceability supplies immutable facts; the compiler supplies semantic
types; Slop and Caret consume projections. No external service or new dependency
is required by the architecture. Offline Git snapshots and opt-in PR metadata
avoid making network access a prerequisite for local queries.

Before implementing a foreign-format adapter, verify the exact upstream schema
and version and add interoperability fixtures. This design does not adopt an
unverified interchange schema or depend on a hosted traceability service.
