# Native array take method missing in database query

Status: source workaround candidate; runtime UNRUN.

Checkpoint74 actual failure: `canonical-batch69/unit-6`, source commit
`8973828b8187c7692f6e8e76489d924cc10c9c26`, producer SHA256
`645e62a815d076d77a61b01daa6e86c1330632686c18ce4c56cccd860a4a714a`.
The native pipeline refuses `row_ids.take(self.limit_count)` in
`src/lib/nogc_async_mut/database/query.spl:154`.

The existing array method contract takes the ordered prefix into a fresh
array. The Rust interpreter's collection method uses `.iter().take(n).cloned()`;
its count helper clamps negative signed values to zero. The existing Simple
`std.nogc_async_mut.array.array_take` implements the same clamped prefix loop.
These sources are contract evidence; no Rust engine is executed or selected
as a fallback.

The bounded source workaround mirrors that loop on `[i64]` row IDs after
filtering/sorting and before existing copied-row materialization. Zero and
negative limits yield empty, longer limits retain all ordered IDs, and no
source view escapes. It avoids relying on negative slice/index behavior.

The generic Simple helper currently has no return annotation; importing its
whole module also adds an unrelated closure to this failing native unit. This
workaround keeps the existing query surface and typed local data path until
the actual native array method is implemented and qualified. Remove it after
actual native `.take` passes the same zero/short/equal/long/negative, sort/filter,
and copy-isolation regressions. The query builder's own `take(n)` API stays
unchanged.

Separate optional table-receiver provenance is a compiler cause, not repaired
by this loop. Do not clear the database unit's failure until a newly built
producer, the exact query source and genuine execution validate both causes.

Permanent native parity plan: extend the existing proven-runtime-array method
owner in `_MirLoweringExpr/method_calls_literals.spl`, alongside
`lower_runtime_array_slice`1833–1909. That owner already calls the existing
`rt_slice(handle,start,end,step)` ABI, provides fresh shallow array storage,
retains element/nominal-owner metadata and drops the original fixed extent.
Native `.take(n)` must check exact one-argument integer shape, evaluate receiver
and count once, and clamp signed count to zero before passing start0/end-count
to the existing slice owner. Passing a negative end directly would mean
from-end slice semantics and is not equivalent. Preserve packed byte/u64
metadata and reject nonarray/unknown receivers and wrong argument types.
Qualify direct/nested-call receivers, nominal element ownership and fresh
storage using the native `.take` spelling, then remove this local loop and
rerun these unchanged query cases. This packet does not implement or claim
that permanent compiler method parity.
