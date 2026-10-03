# Array filter closure calling convention

Four authored frontend→HIR→MIR cases construct actual lambda values: inferred
noncapturing i64, captured i64, captured text, and captured i32 predicates.
Each compares the actual lifted producer signature to the filter consumer,
rejects direct calls through a closure handle, checks environment-first calling,
and requires exactly one static target-resolution instruction for captured input.
One array-read and one push instruction remain in the loop. These are static
shape counts, not observed runtime callback counts.

Captured cases also require a nonzero resolved-target branch. Its failure block
uses the canonical Abort terminator; removing the success edge from the
actual generated CFG must disconnect every indirect callback. This checks guard
dominance rather than merely finding a panic instruction. Runtime allocation
failure injection remains pending.
LLVM translation must emit the actual panic ABI: one pointer and the explicit
42-byte message length. Backend-owned Abort lowering avoids guessing a shared
panic ABI across LLVM, C, Cranelift and pure-runtime providers.

Inspection also found older manual `rt_panic` calls with zero declared params
and one operand elsewhere in method lowering, while LLVM declares `(ptr,i64)`
and the pure core provider has a separate word-shaped entry. Those pre-existing
sites need an owner-boundary audit; this repair changes only the new filter guard.

The repair preserves the existing all-word lambda ABI and capture construction
timing. It does not inline captures, fuse loops, or change type eligibility.
Typed element decoding and text representation remain separate unverified
concerns: the legacy filter decodes elements as i64, and this slice does not
claim text/i32 semantic correctness simply because producer and call agree.
Unsupported lambdas retain the existing unresolved-method diagnostic/rt_panic
path; there is no claimed runtime fallback or silent empty-result substitution.

No build/test runner was invoked. REQ-002 parity and REQ-008 fusion remain open.
