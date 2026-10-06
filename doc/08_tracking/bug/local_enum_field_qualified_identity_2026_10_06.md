# Local enum field qualified identity

Status: candidate; native validation UNRUN. No release admission.

The b4/29f verdict build reports 24 enum-as-struct operator errors across nine
ProcessObservation V4 enum families. Field projection intentionally resolves
provider types by exact owner through `lookup_qualified_type_raw`; local enum
declaration registration never populated that index. Imported enums already
publish after alias renaming. Missing field HIR metadata causes enum equality
to fall through to the genuine-Struct operator diagnostic.

Register only local declared enums, checking scalar kind, spelling, and normalized
owner before first-write qualified publication. Keep imported alias/reexport
registration, generic representation, canonical class allocation, and all MIR
owner/registry checks unchanged. No receipt validation predicate is changed.

Coverage prepared: local equality/inequality, nested field, genuine struct
negative, foreign same-name index exclusion, duplicate publication, first-write
binding, generic declaration index. Imported/reexport fixture controls are prepared, native UNRUN. Whole verdict behavior remains UNRUN.
One dictionary insertion per local enum; no full-table scan or retained cache.
