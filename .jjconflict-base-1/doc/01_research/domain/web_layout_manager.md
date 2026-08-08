# Web layout manager domain research

CSS layout invalidation is dependency propagation, not blanket document dirtiness. Paint-only and compositing-only changes do not require layout; intrinsic measurements, formatting-context rebuilds, DOM insertion, font metrics, and viewport geometry can expand the dirty frontier.

Formatting contexts and containment bound propagation. Incremental correctness is established by comparing against a full CPU layout oracle and recording the visited islands. Unsupported contexts must be rejected before accelerated execution.

The v1 manager follows those constraints with stable arena order, explicit change classes, and framework receipts. GPU algorithms remain a later backend behind the same contracts.

