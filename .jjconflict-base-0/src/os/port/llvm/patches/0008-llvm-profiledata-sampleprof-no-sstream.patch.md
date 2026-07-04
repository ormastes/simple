# LLVM ProfileData SampleProf No-Sstream Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::basic_ostringstream` remains incomplete, so LLVM users of
`SampleProf.h` cannot compile through `std::ostringstream`.

Patch `/home/ormastes/llvm-project/llvm/include/llvm/ProfileData/SampleProf.h`:

```diff
+#include "llvm/Support/raw_ostream.h"
-#include <sstream>
@@
-    std::ostringstream OContextStr;
+    std::string ContextStr;
+    raw_string_ostream OContextStr(ContextStr);
```

The header already exposes `raw_ostream` printing APIs, and
`raw_string_ostream` preserves the same string-building behavior without
requiring libc++ iostream localization support.
