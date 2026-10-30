# Native array range-slice lowering

Status: OPEN. Source workaround awaiting Phase2 runtime verification.

The pinned pure-Simple Phase2 producer rejects array range indexing such as
`history[250..]` during MIR lowering. Retained evidence:
`build/tooling-phase2/t32-cli-process-facade/compiler.log`. This is a compiler
surface limitation, not a reason to drop entries or change history retention.

T32's source workaround uses a typed suffix-copy helper. The original policy
remains: once history exceeds500 entries, discard the first250, preserving
the order and all fields of the remaining entries. Source tests call that
production helper and cover threshold, suffix order and boundary behavior.
They are authored and must not be reported executed without real native results.

The underlying compiler feature remains open. Removal requires native array
range indexing to compile/link and execute with correct element values and
empty/boundary behavior, followed by the original history caller regression.
Do not silently normalize unsupported grammar into a permanent language rule.
