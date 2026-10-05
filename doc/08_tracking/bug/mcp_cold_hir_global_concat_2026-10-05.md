# MCP public path constants retain unresolved HIR types

Status: OPEN. Source workaround prepared; native verification UNRUN.

The restarted small-to-large MCP entry, source
`eec754ab6db092f1dc86e1fc261c2e2ee96d0f6f`, producer
`0aec27aa6ea5f6877ad2aa4a020171ed095ab70ea433463c46633d0edbc5b29b`,
fails cold public-interface publication on `ASSISTANT_STORE_SESSIONS`.
Earlier failures also name `ASSISTANT_STORE_DIGESTS`.

`lower_hir_const_decl` in `_Items/trait_impl_lowering.spl` assigns concrete
types to unannotated primitive literals but falls back to `Infer(0, 0)` for
other initializers, including concatenation. Public ABI publication correctly
rejects that unresolved type. Source annotations let the existing canonical
`lower_type` path supply a concrete `Str`; no receipt validation is relaxed.

The temporary workaround adds `text` annotations to the five shared public
path constants. Names, initializer expressions, values, exports and runtime
storage stay unchanged. The bug remains open until the compiler can infer
these valid unannotated initializers before cold ABI publication. Recovery
reference `02b0f4d546a` identifies the original declarations; it does not
authorize resetting any whole file.

The SSpec and native fixture exercise all five paths, default/whitespace root
selection, and a custom root containing a space. Native acceptance requires
both backend fixture builds, exact eight-check output, and the original MCP
entry build/help smoke. Those checks are UNRUN. No runtime allocation or new
traversal is added by the annotation; measured runtime RSS/performance is
also pending. Existing running source snapshots are unchanged.
