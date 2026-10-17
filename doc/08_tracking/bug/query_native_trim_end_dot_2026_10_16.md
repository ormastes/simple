# Query native trailing-dot method resolution unavailable

Bug ID: query-native-trim-end-dot-20261016.
Status: temporary source workaround; bug DB reconciliation pending qualified tool.
Recovery source:5e9123a377ef9a6278ec1ae6e65954112b84a4de.

Producer0CD6's first native query control build reports unresolved method call:
trim_end at symbol_resolution.spl137:71 and141:76. Those sites parse brace/star
imports using rest.substring(...).trim().trim_end("."). The two MIR failures
also include three unsupported array tail ranges, documented separately.
No objects, linked binary or native behavior PASS resulted.

Workaround: retain the original trim() call, then repeatedly remove one literal
ASCII dot while ends_with(".") holds. substring(0,len-1) is guarded by the
nonempty dot suffix. All trailing dots disappear; interior dots remain. This
does not substitute whitespace trimming for suffix removal and does not claim
text method-resolution support was fixed. Both call sites and the helper carry
immediate workaround/recovery annotations.

The standalone control exercises actual parse_imported_modules on a real
temporary file, checking brace and star imports with repeated trailing dots,
interior dots and an unchanged plain import using count and scalar comparisons.
These added cases are UNCOMPILED/UNRUN pending owner review and cycle2. The
workaround's actual commit is the commit containing this report and annotations;
record its exact SHA with qualification evidence before any done claim.
