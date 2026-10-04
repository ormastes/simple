# Provisional bootstrap omitted plugin and selected kernel roots

The diagnostic Cranelift Phase 3 bootstrap could not resolve
`plugins.backend_registry.full_static_backend_registry`. The frozen checkout
contained the 3935-byte source file, but the SCV snapshot did not: the command
included only compiler, app, lib and os source roots.

Add plugins, package_ownership and compositions to the Phase 3/4 binary
manifest arguments. Place the existing `compositions/kernel_llvm_cranelift`
root first, as the successful Phase 2 build does: the default driver
bootstrap_k1_selected module intentionally reports an unselected policy.
The broad compositions root alone does not select that override.

The manager-image compiler invocation, argv digest and recorded tool-intent
template use the same ordered roots. This repairs source scope without
bypassing SCV or inventing missing modules. The focused argument contract
checks all four sites and rejects removal of each added owner root at each
site. Actual native build qualification remains pending.

Existing running commands, failed logs, immutable receipts and caches remain
preserved. Future diagnostic retries retain their cache directories; normal
source/argv identity checks determine reuse or invalidation. Sealed manager
images require a new invocation identity rather than rewriting old receipts
to accept changed arguments.