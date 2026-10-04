# MCP cold HIR inference failure lacks source context

Status: diagnostic repair prepared; underlying inference failure unresolved.

The source9737/Cranelift776ce2 Phase4 MCP build stops with
`cold-hir-abi-unresolved:unresolved-inference:0:0`. The receipt owner receives
the module and admitted source identity but discarded them from its error.
The new diagnostic retains both identities after the existing error prefix.
Successful ABI payloads, digests, and rejection of unresolved public types are
unchanged. No invalid ABI is admitted and no cache check is disabled.

The regression supplies a real public HIR constant with an unresolved type,
passes a matching source inventory through the actual receipt owner, and
requires an error naming the module/source. It remains UNRUN. A rebuilt
producer must identify and repair the actual MCP declaration before this
product can pass; improved diagnostics alone do not qualify the build.

The lowered-source batch owner also returned on the first receipt error. It
now collects ABI errors from each distinct admitted source in source order and
returns one newline-separated error after visiting the batch. A single error
keeps its prior exact text. Source/inventory authentication failures still
stop immediately; no partial successful receipt list escapes a failed batch.
Four additional regressions cover a valid module followed by two invalid
modules (including a repeated source), and an entirely valid deduplicated
batch, immediate rejection of a module/source binding mismatch after an
earlier ABI failure, and exact single-error text. These native regressions remain UNRUN pending the repaired
producer.
