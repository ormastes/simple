# Concrete pool promotion helpers omit the singleton wrapper rank

BUG-TYPE-POOL-ROOT-RANK-20261016. Database entry pending: no bug database tool
available. Source review found the mismatch in remote 1d8c3a5ab19 after
53afb8c62cb concretized the generic promotion helpers.

The original helper accepted root:[T], instantiated with T=[text], [i64], or
[[i64]]. Every caller intentionally passes [pool], a temporary singleton array
whose element is the actual global pool. The concrete signatures incorrectly
accepted [text], [i64], and [[i64]], dropping one rank. The real arguments are
[[text]], [[i64]], and [[[i64]]]. This is a source contract regression; no native
behavior or failure has been executed for this isolated repair.

The fix changes only those three parameter ranks. Calls, transient promotion,
and rt_array_free(root) remain unchanged. Removing the wrapper instead would
free the live pool rather than the temporary owner container and is unsafe.

The focused regression creates actual primitive, dictionary, union, and named
generic pools in transient scopes, promotes them through the public owner API,
ends the scopes, and checks contents and reuse across a second scope. It is
runtime NOT_RUN pending an admitted compiler/runtime; source assertions or
documentation are not native qualification. Broader compiler/lib/MCP/LSP and
release gates remain UNRUN. This isolated repair excludes the separate mono
alias-placement and initializer-context regressions under review.

The SSpec and standalone type_pool_root_rank_native.spl entry share the same
reason-returning fixture helper. Native main imports no BDD runner, prints a
named failure and returns nonzero for a failed lifecycle or retained value.
The first bounded native qualification is prepared but has not run.
