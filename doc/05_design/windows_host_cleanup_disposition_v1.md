# Host cleanup consumption and diagnostic retention

Status: SOURCE_ONLY / AUTHORED_NOT_RUN. This supersedes the Host close adapter
in the previous genesis-safety snapshot without changing admission or debit
semantics. The lower canonical writer/principal close owner is a separate
reviewed dependency; this lane does not alter its contract or runtime exports.

Only the literal `released` and `consumed-error` dispositions confirm the
originally owned cleanup component has been consumed. Generic `stale`,
`retained` and unknown outcomes preserve the actual cleanup owner. Canonical
prior-closed metadata belongs to the owning pair; an idempotent close may
report its confirmed released/consumed-error result, but Host never infers
consumption from a stale token or path-based substitute. `consumed-error`
supplies a diagnostic while consuming resources; a diagnostic is not itself
evidence that native cleanup remains.

`host_windows_cleanup_disposition_v3` is the production data reducer used for
machine, native and local store progress. It records the first nonempty
diagnostic, keeps ordinary retention transient and classifies unknown states
as pending. It cannot construct authority or native ownership. Native private
cleanup exposes an Option, so production maps only its actual None/Some result
to released/retained; it does not invent a native consumed-error outcome.

Deployment cleanup stores its first error independently of its component
Options. It reads the lower authority/claim/cleanup diagnostic metadata after
close, including a paired writer error while its principal is still retained.
The metadata accessor never reopens a consumed capability. Its actual first
label takes precedence over the generic consumed-error fallback. It clears the machine component immediately after a consumed lower
close, before attempting borrowed native cleanup. If native cleanup remains,
the next turn contains only the actual remaining native owners and the original
diagnostic. It never recloses the consumed machine component. Final completion
can therefore return `closed=true`, no remaining owner and a nonempty error.

Local cleanup similarly retains its first diagnostic across privacy, journal,
store and deployment cleanup. Journal states are adapted from the actual typed
release enum; actual remaining cleanup is retained. Consumed stores are cleared
before later cleanup. Final deployment diagnostics survive the local wrapper.
The established order remains Host journal, machine writer, borrowed native
policy/manifest/root owners. Writer close never releases durable workload debit.

The regression uses the production reducer for the modeled sequence consumed
machine error, retained partner, then released partner, and invokes actual
deployment/local finalization with empty native-owner sets. It does not claim
native fault coverage, actual two-owner close fault injection, compiler
acceptance or runtime qualification. Fresh genesis remains fail-closed pending
a real migration fence; exact retained charge replay is unchanged.
