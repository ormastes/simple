# Clang Lex PPMacroExpansion No-Put-Time Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::stringstream`, `std::locale`, and `std::put_time` are unavailable.

Patch `/home/ormastes/llvm-project/clang/lib/Lex/PPMacroExpansion.cpp`:

```diff
-#include <iomanip>
-#include <sstream>
@@
-    std::stringstream TmpStream;
-    TmpStream.imbue(std::locale("C"));
+    SmallString<32> Result;
+    llvm::raw_svector_ostream TmpStream(Result);
@@
-      TmpStream << std::put_time(TM, "%a %b %e %T %Y");
+      formatTimestamp(TM, TmpStream);
```

`formatTimestamp` uses LLVM `format` and fixed English weekday/month names, so
`__TIMESTAMP__` keeps Clang's C-locale spelling without libc++ iostream
localization support.
