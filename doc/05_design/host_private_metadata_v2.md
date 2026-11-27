# Installed Windows private metadata loader

Status: source implementation and authored specifications; **NOT_RUN** for all
runtime cases, including pure cases. No compiler, bootstrap or Windows native
test campaign was started or retried. This is an additive public-data loader,
not a completed Windows enrollment or service-readiness implementation.

The loader accepts a trusted administrator-selected root and four canonical
SHA-256 pins for the exact installed raw bytes. It opens the native
`WindowsPrivateRootV1` capability and reads fixed children only:

| Child | Trusted pin | Returned representation |
| --- | --- | --- |
| `authority-policy.sdn` | `policy_digest` | Existing `LocalAuthorityPolicyV1` decoder |
| `host-config.sdn` | `configuration_digest` | Existing `HostConfigV1` decoder |
| `engine-policy.sdn` | `engine_policy_digest` | Exact UTF-8 text, opaque to this loader |
| `broker-policy.sdn` | `broker_policy_digest` | Exact UTF-8 text, opaque to this loader |

Each source must contain 1..1,048,576 bytes; the total bound is 4,194,304 bytes.
Every pin is canonical lowercase hex. The decoder validates every raw-byte
digest before attempting any text or policy/configuration parsing. The shared
UTF-8 codec must round-trip the exact bytes, preventing replacement or BOM
normalization. Engine and broker interpretation remains with their respective
owners. Loading their bytes does not validate their backend or grant authority.

The ready metadata owner retains the root and all four readonly native file
generations. Refresh reads those exact handles at offset zero, checks current
file identity/privacy, checks the retained root and ancestor privacy before
and after reading/decoding, and applies the original pins again. It never
reopens a root by path, reloads policy through the POSIX loader, or acquires
clock authority. The native owner denies replacement while these files are
retained; policy rotation therefore requires deliberate close/drain followed
by new verified administrator pins and a new open. It is not automatic reload.
Refresh is an explicit bounded validation operation, not a polling loop or an
unqualified per-request hot-path cache policy.

Open returns metadata Ready, Rejected, or CleanupRequired with the shared
`HostServicePrivateCleanupV2`. Every failed native admission contributes its
typed pending file/root owner before cleanup. Every later read, security,
digest or decode error also routes every acquired resource through that same
cleanup helper. Refresh returns optional updated owner, optional new metadata,
optional pending cleanup and an error. On failure both owner and metadata are
nil. Native close sets each canonical generation cleanup-only before a
fallible close, so copied file values cannot retain read authority during
pending cleanup. Callers must retain pending cleanup and block admission;
closing metadata does not prove that a separate host, provider, native process
or journal owner has closed. A stale copied owner is not a new cleanup grant.

The enum's Ready variant means verified private **metadata only**. A future
factory must independently verify signed static enrollment, the physical
machine claim, selected backend/provider observation, a fresh service epoch,
and acknowledgement after reconciliation against the same retained ledger.
This module contains no factory, runtime-ready marker, provider observation,
journal transition, enrollment lock, cleanup grant, or readiness receipt.
Raw enrollment-lock exposure remains outside this slice.

The source is authored against these actual immutable dependencies:

- Windows generation owner: release
  `635294131cca3a7ff7c8fe552e566fd69e9e6e7c`, PR 7748. The existing worktree
  materializes that released owner as dependency-only commit `28daf4d36ff`;
  root integration must not duplicate it.
- Retained-root current-security facade method: separate four-line commit
  `eb6ab9bd17c`, delegating the existing native ready query. It adds no ABI or
  native implementation.
- Shared private cleanup helper: exact commit `60df4d058e4`, module
  `host_service_private_receipt_v2`. This dependency remains external to the
  isolated worktree; its actual source was reviewed read-only. No copied helper
  or fabricated substitute was added.

Root owns assembling that dependency graph and completing host/controller
admission. Missing graph materialization and lack of runtime qualification are
explicit limits, not a reported source or runtime PASS. Focused cases cover
pure pin/size/codec refusal and actual Windows private-file open, refresh,
cleanup, missing files, digest mismatch and a provisioned foreign-read ACL
root. Their fixtures carry synthetic public data only; they do not attest
signatures, installed enrollment, engine execution or live service readiness.
