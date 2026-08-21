# SimpleOS loader-owned image execution authority gap

Status: open, release-blocking for filesystem execution

The former value-level consume API and its public reset/reseed/test-mint seams
are removed. The loader now owns one bounded typed slot capsule behind the
canonical checked raw mutex. Owner copies carry only the singleton epoch;
commit, retrieval, close leasing, close completion, slot reuse, generation
advance, and nonce advance all linearize under that mutex. Lock or unlock
failure returns `SerializationUnavailable`. Failed handle close moves the slot
to `CloseRetryable`, keeps it active and unreusable, and permits a fresh
single-owner close lease. There is no public reset or mint surface.

Caller-constructed verification booleans still cannot mint a token. The only
issue seam is package-private for the future cryptographic verifier, while
admission closes the open handle and returns
`CryptographicVerifierUnavailable`.

Execution remains release-blocking. The returned retrieval value explicitly
sets `execution_authorized=false`. A private bounded x86_64 consumer now reads
and re-hashes the exact retained handle, rebuilds and compares the ELF process
image, maps through the scheduler-owned mapper, and retains the resulting
address space until whole-space release and retryable handle close. It does not
expose that address space or authorize execution. There is still no admitted
cryptographic verifier, scheduler seam accepting an already-mapped lease, or
reclaiming ARM64/RISC-V address-space destroy owner. Production bootstrap must
supply a unique high-entropy nonce seed. Closure still requires those owners
plus executable replay, close-failure cleanup, generation-retirement, and
concurrency evidence under the admitted self-hosted runtime.

## Evidence blocker

The focused public-surface spec covers exact/conflicting initialization,
copied-owner observation, forged-token rejection, and non-mutation. It has not
been executed in this change because runtime/bootstrap execution was explicitly
disallowed. Live issue/replay/concurrent-commit/close-retry/generation-retirement
coverage is also BLOCKED: tests outside `os.kernel.loader` cannot import the
package-private verifier/close seams under strict visibility, and widening
those seams or adding a production-callable test mint is not acceptable. That
evidence must come through the real package-private cryptographic verifier
integration. No admission or execution readiness claim follows from this slice.
