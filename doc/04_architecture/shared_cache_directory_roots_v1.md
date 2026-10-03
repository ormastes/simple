# Shared-cache directory ownership

REQ-004/007 require a physical storage boundary before private frontend state
and portable immutable cells can coexist. The compiler asks the SOSIX directory
facade to admit its root pair. SOSIX re-exports the canonical no-GC synchronous
I/O owner; only that owner calls the native directory capsule. Compiler leaf
modules contain no OS-handle operations or mutable admission registry.

The native capsule owns open fd/handle lifetimes, generation tokens, physical
ancestry, cold private-root creation and mutex-protected rejection state.
Existing descriptor identity contracts cross the facade; native handles never
enter portable cache cells. Closing a token consumes ownership. The compiler
memo retains its own token until rejection or process exit and is bounded.

Windows and Linux are platform implementations of the same admission contract,
not copies of cache policy. Unsupported hosts/paths fail closed. Source receipt,
parser identity, cfg/features, cell validation and AST hydration remain their
existing owners' responsibility. Directory identity is necessary but cannot
substitute for those checks or capacity/session admission.

The boundary guarantees separation at validation time. Existing pathname-based
cache I/O is outside its transaction scope. Deployment therefore needs trusted,
owner-controlled ancestors. An adversarial mutation guarantee would require a
separate descriptor-relative read/publish transaction and is not claimed here.
Details, performance cost and actual evidence are in
`doc/05_design/shared_cache_directory_roots_v1.md` and
`doc/03_plan/sys_test/shared_cache_directory_roots_v1_evidence.md`.
