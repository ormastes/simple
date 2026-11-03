# Native macOS runtime-cache fingerprint scenarios

Executable source:
`test/01_unit/compiler/backend/runtime_posix_cache_fingerprint_spec.spl`.
Status: manually maintained scenario map; **Simple execution and SPipe docgen
are pending a qualified runner**. Native shell diagnostic evidence is narrower
and does not qualify this SSpec.

The scenarios use a private temporary C/header tree and stock
`PATH=/usr/bin:/bin`. They exercise the production command builder rather than
implement a second fingerprint algorithm in the spec.

| Scenario | Required observation |
|---|---|
| Stable fingerprint | Source names with spaces/apostrophes and quoted flag values yield 40 lowercase hexadecimal digits; identical material yields identical keys. |
| Invalidation | Editing source bytes, adding a header and changing semantic flags each change the key. |
| Incomplete authority | Missing source root, failed compiler version and empty compiler version yield nonzero status and no key. |
| Hash failure | A private PATH fixture whose shasum exits 7 must produce no partial key. |

The native scenarios are restricted to macOS. Windows keeps its separate cache
implementation. No cross-platform runtime qualification is inferred from this
host-specific scenario set.
