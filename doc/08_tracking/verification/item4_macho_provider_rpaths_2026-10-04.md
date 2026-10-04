# Mach-O provider runpath verification

STATUS: FAIL — full item4/Phase 4, SDK and five-host qualification remain open.

This increment preserves validated binary LC_RPATH and selected v5 text-provider
runpaths, passes their physical owner through the V2 closure callback, and wires
the native adapter to that callback. V1 callers retain an explicit refusal for
external @rpath requests. Hosted linker selection remains opt-in.

The documented link-time profile uses only the requesting provider's runpaths.
It is Apple-derived, not a claim of universal LLVM parity or dyld runtime-chain
behavior. Existing declared-inline catalog precedence is a project policy.
Standalone providers resolve per owner/name/ordered-path context; different
physical paths for the same install identity are rejected before publication.
Explicit SDK roots exclusively reroot POSIX absolute runpaths. Actual declared
absolute paths remain usable without an SDK root; relative CWD-dependent paths
are refused. Owner/output host path normalization is separate from forward-slash
Mach-O metadata syntax.

Initial executable intent 778d112811c preceded production edits. Seven authored
scenarios through f64c60b4f56 cover x64/ARM64 binary and v5 native link routes,
real V2 filesystem lookup, malformed commands, ordered first-candidate failure,
output preservation, owner-context conflicts, inline precedence and cycles.
Later review cases accompany implementation; no executed RED/GREEN is claimed.
LLVM fixture construction/inspection provides independent format evidence only.

Core 78194e42070 and native integration ccb9ae0c20b received independent source
review with no concrete P0/P1 findings. Graph byte limits count every delivered
callback read, including cached physical paths. These are logical accounting
bounds, not allocation, no-swap, authority, or measured process-RSS guarantees.

Both shared and integration bin/release directories were absent at this turn's
check. Simple compilation, SSpec, docgen, coverage, core/lib/MCP, native host and
performance checks remain UNRUN. No Rust seed fallback was used. Legacy SDK
reexport commands, broader provider semantics, complete application integration,
managed admission and all five native host qualifications remain open.
