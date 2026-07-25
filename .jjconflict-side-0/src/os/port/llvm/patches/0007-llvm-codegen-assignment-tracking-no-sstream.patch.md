# LLVM CodeGen Assignment Tracking No-Sstream Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::basic_stringstream` remains incomplete, so LLVM CodeGen cannot instantiate
`std::stringstream` in `AssignmentTrackingAnalysis.cpp`.

Patch `/home/ormastes/llvm-project/llvm/lib/CodeGen/AssignmentTrackingAnalysis.cpp`:

```diff
-#include <sstream>
 #include <unordered_map>
@@
     std::string String;
-    std::stringstream S(String);
+    raw_string_ostream S(String);
```

`raw_string_ostream` is already available through LLVM's `raw_ostream.h` include
and preserves this debug formatting path without requiring libc++ iostream
localization support.
