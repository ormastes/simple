# Array filter closure calling convention

Four authored frontend→HIR→MIR cases construct actual lambda values: inferred
noncapturing i64, captured i64, captured text, and captured i32 predicates.
Each compares the actual lifted producer signature to the filter consumer,
rejects direct calls through a closure handle, checks environment-first calling,
and requires exactly one static target-resolution instruction for captured input.
One array-read and one push instruction remain in the loop. These are static
shape counts, not observed runtime callback counts.

Captured cases also require a nonzero resolved-target branch. Its failure block
calls rt_panic and terminates unreachable; removing the success edge from the
actual generated CFG must disconnect every indirect callback. This checks guard
dominance rather than merely finding a panic instruction. Runtime allocation
failure injection remains pending.

The repair preserves the existing all-word lambda ABI and capture construction
timing. It does not inline captures, fuse loops, or change type eligibility.
Typed element decoding and text representation remain separate unverified
concerns: the legacy filter decodes elements as i64, and this slice does not
claim text/i32 semantic correctness simply because producer and call agree.
Unsupported lambdas retain the existing unresolved-method diagnostic/rt_panic
path; there is no claimed runtime fallback or silent empty-result substitution.

No build/test runner was invoked. REQ-002 parity and REQ-008 fusion remain open.
