# Canonical i686 rejected by strict MIR context preparation

Status: source repair; executable qualification pending.

At release ce5b5d9759ca4d6b2c7e59e69ec6de65342139ca, LLVM's strict
target classifier accepts i686, but mir_target_context_from_explicit rejects
it as a lossy architecture. The legacy normalizer reduces i686 to x86 without
retaining generation. The baremetal-x86 request also produces
i686-unknown-none, absent from the strict context vocabulary.

Retain i686 in MirTargetContext.subarch while keeping arch=x86, admit that
canonical architecture and its exact unknown-none spelling. The existing
13-field identity already includes subarch; collection capability admission
remains unchanged. Other x86 generations and LLVM's generic x86 alias stay
outside this correction. This is API compatibility, not driver migration or
cross-target execution qualification.

The existing explicit-context SSpec now covers Linux, Windows, bare-metal,
strict/legacy identity equality, generic-x86 identity separation, LLVM 32-bit
triple compatibility and malformed/incompatible rejection. New assertions are
UNEXECUTED. Runtime verification is waived for this bugfix landing by the user;
no bootstrap, full suite or backend execution PASS is claimed.

Ownership check found no matching i686 context bug shard. The repository claim
helper remains unusable on this host due its previously recorded BSD awk
multiline-value error and early undefined die path; it was not rerun unchanged.
Source work is isolated in work/i686-context-20261115.
