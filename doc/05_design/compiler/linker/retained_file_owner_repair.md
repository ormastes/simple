# Retained-file sequential ownership repair

`RetainedFile` is a value owner. A free function receiving it by value cannot
publish scalar cursor/closed updates to its caller. The sequential API is now
`me read(maximum)`, `me read_exact(count)`, `me write(bytes)`, `me close()`.
Callers retain a `var` owner, including across errors. No legacy mutating free
wrapper remains, since it would silently preserve the ownership defect.

Writes advance position/size after each completed native write, before a later
write can fail. Quota arithmetic rejects position greater than maximum before
unsigned subtraction. Close marks the owner closed and clears its handle before
calling the native close exactly once; failure does not authorize a retry on a
possibly reused descriptor. Exact reads retain consumed cursor on truncation.

Positional reads, identity checks and sync remain read-only free helpers. Windows
positional restore failure returns an error without closing a copied owner.
Sequential reads reapply the authoritative logical position before ReadFile,
so a prior failed restore cannot silently change subsequent sequential data.
The caller must still close its original owner on every error path.

SCV hydration uses a private mutable reader holding input/output owners. A write
to an unwrapped output is stored back before propagating its Result, and output
ownership is removed from that wrapper before final sync/close. This avoids
introducing a second copy-state defect in an intermediate helper.

Evidence: source-only; native integration tests **UNRUN**. Authored regressions
cover cumulative quotas, exact/native cursor progress, positional/sequential
interleaving, truncation progress, closed-handle reuse and close-once behavior.
Linker archive/ELF/stream/spill consumer migration belongs to the research lane.

Adjacent blocker: the existing `Sha256StreamV1` free update/finalization API also
mutates value copies. Its repair is separate; this retained-file change does not
claim that SCV hashing or hydration has been executed successfully.
