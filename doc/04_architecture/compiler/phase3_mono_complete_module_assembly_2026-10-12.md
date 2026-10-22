# Complete archived mono module assembly

`mono_archive_assemble_module_v1` consumes the actual completed root/FIFO execution
ledger. It refuses incomplete coverage, wrong owners and nested scopes. Inside
one owned scope it decodes the original complete module once, reads only the
selected complete generated function records for that module, restores actual
specialization symbol rows and the same final owner counter as the retained pass,
then invokes the existing `prune_consumed_templates` method.

The archive-mode pruning method receives only the emitted mangled-name to exact
template-name index from completed FIFO entries. It still refuses to prune a
template recorded as unresolved, requires an actual emitted specialization, and
keeps non-generic functions and zero-instantiation templates. Its retained mode
keeps the existing complete-function index and behavior. Struct/class/enum bodies,
traits, implementation blocks, globals, initializer/default expressions, source
metadata and symbol tables remain complete in the assembled module. No provider
projection or placeholder body is introduced.

Only the assembled descriptor and cache diagnostic text owner are promoted before
scope close. The descriptor binds original input archive, complete output digest,
original warning digest, ordered root/actual FIFO record coverage, closed state
digest and final symbol counter. Its key is a separate stage/version domain. The
borrowed `mono_archive_load_assembled_module_in_owned_scope_v1` requires an actual
active/unpaused scope and verifies exact original authority, stage, key, complete
body identity, counter and warning identity before returning actual HIR. The
parent owns that returned module and must clear warning aliases and preserve
cache diagnostics before closing its lease.

This artifact is explicitly `mono-assembled-unverified-v1`. It is not
`mono-final-module-v1` and must not admit MIR. Aggregate post-mono verification
still needs its full closure index before any module walk, every existing invariant
counter and ordered violation, and the driver's existing diagnostic/feature policy.
The future final repository reader must bind that actual validation receipt.
No boolean or caller-provided digest substitutes for those consumers.

The native fixture adds actual complete-module codec digest parity with the
retained root and provider modules, including specialization rows, pruning and
final counters. It also checks inactive borrowed reads, nested assembly refusal,
and refusal when an unverified descriptor is changed to claim the final stage.
Existing incomplete-execution and missing-root controls now call the real
assembler too. The mono launcher requires 75 checks; compilation/execution remain
pending root serialization. Static guards are not native evidence. No full driver
activation, reclamation of original promoted HIR or RSS improvement is claimed.

Next work is the exact two-phase aggregate verifier lease: shared actual closure
index extraction with compact delta publication, then the existing exhaustive
per-module walker with text-only report escape and unchanged transport limits.
After that owner and the driver policies admit the actual reports, a final
repository can publish immutable ordered complete-module descriptors for MIR.

The original complete-body reader is the shared actual helper from dependency
`411f2c4ef55c4b1a684c85d6d48570d72d491da7`, rather than a duplicate decoder or
parallel authority implementation. This patch requires that helper and the prior
selected-provider input key/publication schedule chain before native compilation.
