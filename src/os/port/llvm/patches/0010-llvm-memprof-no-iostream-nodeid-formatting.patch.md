# LLVM MemProf No-Iostream Node ID Formatting Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::stringstream` and `std::hex` are unavailable.

Patch
`/home/ormastes/llvm-project/llvm/lib/Transforms/IPO/MemProfContextDisambiguation.cpp`:

```diff
-#include <sstream>
@@
-    std::stringstream SStream;
-    SStream << std::hex << "N0x" << (unsigned long long)Node;
-    std::string Result = SStream.str();
-    return Result;
+    return ("N0x" + Twine::utohexstr((uint64_t)Node)).str();
```

This keeps DOT node id formatting local and uses LLVM's existing `Twine`
hex helper instead of depending on libc++ iostream localization support.
