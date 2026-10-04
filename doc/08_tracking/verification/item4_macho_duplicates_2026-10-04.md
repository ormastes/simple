# Mach-O duplicate-definition policy verification

STATUS: FAIL — full item4/Phase 4 and five-host execution remain incomplete.

Ordinary native-build and request-projection configurations enable duplicate
definitions. The strict-only Mach-O adapter rejected that value before linking.
This change must implement real deterministic first-selected strong-definition
selection and propagate it through archive resolution and final layout binding,
while preserving false/default strict duplicate failures.

Acceptance uses real competing object/archive inputs and independently inspected
output bytes, with strict rejection preserving a destination sentinel. Resolver
weak/common precedence is distinct from hosted weak-coalescing support, which
remains unimplemented. No assertion alone proves loader/native execution.

Compilation, executable SSpec, docgen, coverage, compiler/lib/MCP/native smoke,
performance and all-host execution remain UNRUN without an admitted deployed
self-hosted runtime. Structural/source evidence will be recorded separately.
