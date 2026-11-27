# Legacy native-owner lookup retains temporary alias graphs

Attempt12 full CLI again exceeded the 48 GiB process-tree RSS cap. Its worker graph diagnostics reported more than 24,000 legacy owner checks, with epoch checks, owned scopes, and nested scopes all zero. Target/cfg preprocessing flags were false and memo counts zero. Therefore the prior epoch-only scratch boundary did not execute on this workload.

The legacy owner check calls the existing cached source scanner, then constructs physical and walked alias names and SourceFile arrays on every membership query. The result is only a boolean. Those temporary graphs need not remain allocated for the process lifetime.

The repair retains cache scanning/publication outside a new scratch lease, runs the unchanged alias policy inside it, and closes the lease before returning the boolean. Caller-owned scopes are never closed. Physical path spelling, shadow resolution, content cache reset/invalidation, and epoch validation are unchanged. Platform lazy state is warmed before the lease.

Ownership contract: each compiler worker owns its source caches; input path/content are borrowed retained values; alias arrays and generated path/name strings are lease-local; only a scalar ownership decision escapes. Cache writes are excluded from the new lease. No new memoized source authority is introduced.

The native fixture exercises real compiler-file aliases repeatedly, verifies cache content/import/sibling retention, checks one source scan and one lease per nonnested lookup, and verifies that a caller-owned lease remains active until the caller closes it. Runtime validation is pending. This change does not establish full CLI success, fix the separate source-table retention issue, or prove a particular RSS reduction. Cached scan/path work outside the lease still allocates.
