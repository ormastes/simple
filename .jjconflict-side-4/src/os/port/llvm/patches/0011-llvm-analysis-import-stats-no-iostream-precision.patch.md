# LLVM Analysis Import Stats No-Iostream Precision Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::stringstream` and `std::setprecision` are unavailable.

Patch
`/home/ormastes/llvm-project/llvm/lib/Analysis/ImportedFunctionsInliningStatistics.cpp`:

```diff
+#include "llvm/Support/Format.h"
-#include <iomanip>
-#include <sstream>
@@
-  std::stringstream Str;
-  Str << std::setprecision(4) << Msg << ": " << Fraction << " [" << Result
-      << "% of " << PercentageOfMsg << "]";
+  std::string Str;
+  raw_string_ostream OS(Str);
+  OS << Msg << ": " << Fraction << " [" << format("%.4g", Result) << "% of "
+     << PercentageOfMsg << "]";
```

This keeps the original four-significant-digit display intent without requiring
libc++ iostream localization support.
