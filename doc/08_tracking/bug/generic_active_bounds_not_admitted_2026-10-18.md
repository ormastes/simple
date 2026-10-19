# Generic calls bypassed active HM bound admission

The active driver invokes `HmInferContext.infer_module`, but that entrypoint did not invoke the declaration collectors or solver. A declared `choose<T,U>` with `U:Marked` could not enforce U at an actual call. The prior binder-mapping repair fixed a helper and intentionally left this production gap open. Explicit `identity<i64>(1)` also reached a rigid Named(T) signature instead of an instantiated signature.

Candidate repair uses the existing HM and trait-solver owners, with real infer_module scenarios. It requires the reviewed conditional-obligation solver packet; that dependency is pinned in the source manifest. No binary, compiler, Lean, or test runner was launched.

Still open: actual parsed-source generic bound/default transport. Core/parser-to-flat bridge currently reconstructs ParserTypeParam with bounds=[] and has_default=false. This is a separate causal loss; injecting real HIR bounds in the current suite proves only this active HM layer once run. Full compiler admission additionally depends on driver severity and the remaining method/cross-module/parameterized-trait and generic conformance obligations documented in the design.

Revision 2 addresses independent ACTIVE-HM-001: symbolic forwarding previously matched IDs before validating their symbol-table rows. Complete declaration authority is now validated before publication, with real malformed-input infer_module controls. This is a source candidate correction, not runtime evidence.
