# Current-body mono continuation

The closed current-body continuation invokes the existing current execution
creator, ordered root consumer, growing FIFO consumer, completed-ledger check,
immutable applied-selection capture and complete-body verification replay.
Each underlying consumer retains its existing owned-scope lifetime. The
continuation accepts no report or cleanliness flag and retains only compact
execution state, artifact descriptors and the actual rendered report.

`driver_hir_archive_current_mono_execute_v1(current, inventory, mono_order)`
requires an inactive transient owner and returns the actual execution together
with its independently reconstructed verification result. It preserves the
root barrier, specialization deduplication, recursive-depth refusal, counter
allocation, emitted-only pruning and diagnostic accumulation. A refused
schedule or occupied owner fails before execution creation. A completed owner
cannot be submitted again as fresh registration.

The companion statistics projection maps all six actual execution counters to
the existing `MonoStats` publisher input. It grants no validation authority.
This continuation does not mutate `CompileContext` or publish policy results.
The production factory must first obtain genuine source/journal/full-gate,
weave, cold-capture and configured quiet/current prerequisite ownership, then
capture fresh current registration in the authoritative mono order. After
execution it must register the actual execution and verification capture with
the driver private authority, publish the existing mono warning/diagnostic and
post-mono policy in retained order, and install the genuine final read pin.

MIR declaration firstwinner order remains a separately admitted source/layout
schedule. Logical alias labels and semantic pass order belong to the driver
prerequisite owner; this mechanical continuation cannot infer either from
canonical module names or mono order. No final repository/read API or bounded
production activation is supplied by this patch.

The current-mono native fixture grows from 20 to 27 positive guards. Its added
controls use freshly captured complete transformed bodies and the actual
continuation: reversed-order refusal before mutation, active/paused refusal,
complete root/FIFO coverage, diagnostic/statistics parity, real 99-valued
specializations and complete module/report parity, repeat-owner refusal, and
replay after another scratch scope has grown and closed. Its transform boundary
is explicitly mechanical; the launcher still requires actual admitted producer
and runtime/provider authority. All 27 guards remain UNRUN pending a root-owned
native slot. Source checks cannot qualify execution, reclamation or CLI RSS.
