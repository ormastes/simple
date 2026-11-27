# Compiler written-Any diagnostic visibility

Status: implemented; execution verification pending.

Previously, explicit `Any`/`any` reached the existing HIR type-lowering
diagnostic only when the driver selected robust or critical compiled policy.
Other policies could silently accept the annotation. Bootstrap warning relays
also suppressed recovered diagnostics.

The existing type traversal now records `W-ANY-COMPILE-001` under the lenient
policy and retains `E-ANY-COMPILE-001` under the strict policy. Only a validated
`unsafe(capabilities: [type_erasure])` block authorizes the annotation; unrelated
or unknown capabilities do not grant authority. Closures reset inherited grants.
All five existing driver warning routes print the mandatory warning, including
cached HIR and bootstrap paths. The HIR cache header advances to v4 so older
entries without the warning are rejected through existing validation.

NEVER disable this diagnostic for a workaround, bootstrap, cache reuse, or
execution mode. Repair the type or use an explicitly authorized type-erasure
boundary.

The patch adds no whole-module source scan, whole-AST pass, compiler subprocess,
or cache deletion. Alias registration recursively checks only the authored
`TypeKind` syntax in that alias target and its present type-parameter defaults;
it does not resolve alias references. Diagnostic output and this bounded
traversal still incur work; performance has not been measured. Direct AST
interpreter paths are outside this patch's qualification scope.

Regression specifications cover severity, capability validation, closure scope,
source-spelled `__any` rejection, direct/nested alias syntax, forward aliases,
parser fallback distinctions, and cold/warm native-build warning delivery.
They do not yet include a generic alias or type-parameter-default regression.
The unit and integration specifications have not run: this checkout has no
qualified self-hosted compiler/test runner. Required compiler/library and
MCP/LSP verification remains pending. Source review is not a verification PASS.
