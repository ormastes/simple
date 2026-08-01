# LLVM Coverage Mapping No-Sstream Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::ostringstream` is unavailable.

Patch
`/home/ormastes/llvm-project/llvm/include/llvm/ProfileData/Coverage/CoverageMapping.h`:

```diff
-#include <sstream>
@@
-    std::ostringstream OS;
+    std::string Str;
+    raw_string_ostream OS(Str);
```

Apply the same local replacement in the MCDC helper string builders:

- `getConditionHeaderString`
- `getTestVectorHeaderString`
- `getTestVectorString`
- `getConditionCoverageString`

This keeps coverage mapping formatting on LLVM's existing raw stream utility
instead of requiring libc++ iostream localization support.
