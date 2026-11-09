# Native `me` method loses `self.field` write (P1, silent wrong value)

Status: fix-implemented-verification-pending (fix landed via PR #7998).

Repro: `test/s3sanity/me_writeback.spl` (siblings: `me_writeback_siblings.spl`).
Native stage2_new4 (base 1f0674fc682) prints `n=2`; interpreter prints `n=5`.
All siblings (class local, struct local, nested class/struct field receiver,
class/struct array element) print 2 natively: the defect is in the callee.

Root cause: collection_desugar rewrites `self.n = self.n + y` to
`self.n.merge(y)`; `merge` was missing from `is_mutating_method`, so the
field write-back was never emitted. LLVM IR of `Box.bump` loaded `self.n` into
an alloca and returned without storing it.

Evidence: `test/01_unit/compiler/50.mir/me_method_field_writeback_spec.spl`
is red at 1f0674fc682 (no SetField), green at 110719b6d2a, and red again when
only the `merge` entry is disabled. Native re-verify needs a stage2 rebuilt
from a commit containing 1e5c263034a.
