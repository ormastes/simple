# BUG-2026-10-18-NATIVE-ENTRY-OBJECT-CLI-REGISTRATION

Status: source repair; native qualification pending. Bug database reconciliation
pending: the normal database tool is unavailable in this session.

The public bootstrap help and output argument owner advertise and map
`--emit-entry-object` to the existing driver wire value `entry`. The normal
native-build coordinator on release_phase3 base
`2bcc8144b1bf4b16af66d6c0a5c9bd76e1c3ac8f` rejects that flag as unknown before
compilation. Its parser and output-mode binding also omit the entry variant.
The old ee3 producer exhibited this rejection during independent qualification;
this product fix does not modify that frozen producer or its live build.

The normal coordinator now accepts and parses the flag, includes it in output
mode mutual exclusion, binds `entry`, and performs entry closure discovery.
Entry object output uses native-only format, removes executable launch metadata,
and declares an object artifact to native action admission. Existing output
mode snapshot/restoration remains in effect.

Behavior regressions exercise actual bootstrap worker argument normalization and
normal option validation (including a misspelled negative control), the shared
output parser across all four modes and twelve ordered conflicting pairs, and
entry-mode environment binding/restoration. They do not prove emitted object
contents or complete normal coordinator execution.

Native specs, compiler/core checks, and emitted-object qualification are UNRUN:
no qualified pure-Simple full CLI is available for this isolated lane. Source
review and repository guards are not a native PASS. No Rust seed test fallback,
compiler launch, or live cache mutation was performed.
