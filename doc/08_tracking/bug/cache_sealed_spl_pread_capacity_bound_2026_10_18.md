# Sealed cache SPL read capacity bound (2026-10-18)

The initial retained-sealed facade accepted both an output byte array and an unrelated capacity scalar. A caller could pass a scalar larger than the actual array, allowing the native read contract to write beyond that array. The existing ordinary READ facade already prevents this by deriving capacity from out.len().

The sealed facade now follows that same owner pattern: mut out:[u8], and native capacity is exactly out.len(). The independent scalar parameter is removed. No existing callers are present in base8d482bfc. The native C ABI and its raw-pointer capacity contract are unchanged.

Validation is source-contract comparison with the existing READ facade and diff checks. The separate focused SPL fixture is prepared but native execution is UNRUN; it checks actual returned bytes and rejects an undersized output array when later admitted. The earlier59 C ABI checks are not rerun for this SPL-only correction and do not establish native SPL facade qualification. Broad driver integration and public entry-object publication remain pending.
