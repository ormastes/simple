# Query native trailing-dot method resolution unavailable

Bug ID: query-native-trim-end-dot-20261016.
Status: temporary source workaround verified by the native query control;
bug DB reconciliation pending a qualified tool.
Recovery source:5e9123a377ef9a6278ec1ae6e65954112b84a4de.

Producer0CD6's first native query control build reports unresolved method call:
trim_end at symbol_resolution.spl137:71 and141:76. Those sites parse brace/star
imports using rest.substring(...).trim().trim_end("."). The two MIR failures
also include three unsupported array tail ranges, documented separately.
That first attempt produced no objects, linked binary or native behavior PASS.

Workaround: retain the original trim() call, then repeatedly remove one literal
ASCII dot while ends_with(".") holds. substring(0,len-1) is guarded by the
nonempty dot suffix. All trailing dots disappear; interior dots remain. This
does not substitute whitespace trimming for suffix removal and does not claim
text method-resolution support was fixed. Both call sites and the helper carry
immediate workaround/recovery annotations.

The standalone control exercises actual parse_imported_modules on a real
temporary file, checking brace and star imports with repeated trailing dots,
interior dots and an unchanged plain import using count and scalar comparisons.
These added cases passed in the final native control described below.

## Final scoped qualification

Workaround commit: `2081277b2fe12fc39057519313d5f16c9ce57a78`.
Qualified code source: `3a3e5628c3cbe31d317ef299b0fc7f2fb666dbc5`.
Producer SHA256:
`0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b`.
Candidate SHA256:
`587c774f14d0c297e6f76b43c0e5a82b4c00c94cc9fdbb1cbba70a15defb1cc0`.
The first native control execution passed with exit0, empty stderr and stable
hash. The real temporary import file covers brace/star imports with repeated
suffix dots, preserved internal dots and a plain import. All56 original SPL
objects remain byte-identical in a standard lazy archive; canonical8-init entry
and38 current-source C objects link without FORCE, ignored unresolveds or stubs.
See the sibling boundary-header report's evidence directory. This verifies the
reachable query workaround, not text method-resolution support, unavailable
full CLI capabilities, compiler generation admission or deployment. Bug DB
reconciliation remains pending.
