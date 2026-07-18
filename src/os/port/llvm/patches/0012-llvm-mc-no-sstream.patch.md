# LLVM MC No-Sstream Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::ostringstream` is unavailable.

Patch `/home/ormastes/llvm-project/llvm/lib/MC/MCPseudoProbe.cpp`:

```diff
-#include <sstream>
@@
-  std::ostringstream OContextStr;
+  std::string ContextStr;
+  raw_string_ostream OContextStr(ContextStr);
@@
-    if (OContextStr.str().size())
+    if (!First)
       OContextStr << " @ ";
+    First = false;
```

Patch `/home/ormastes/llvm-project/llvm/lib/MC/MCParser/AsmParser.cpp`:

```diff
-#include <sstream>
@@
-    std::ostringstream MaxNestingDepthError;
-    MaxNestingDepthError << "macros cannot be nested more than "
-                         << MaxNestingDepth << " levels deep."
-                         << " Use -asm-macro-max-nesting-depth to increase "
-                            "this limit.";
-    return TokError(MaxNestingDepthError.str());
+    std::string MaxNestingDepthError;
+    raw_string_ostream OS(MaxNestingDepthError);
+    OS << "macros cannot be nested more than " << MaxNestingDepth
+       << " levels deep."
+       << " Use -asm-macro-max-nesting-depth to increase this limit.";
+    return TokError(OS.str());
```

Patch `/home/ormastes/llvm-project/llvm/lib/MC/MCParser/MasmParser.cpp` with
the same macro nesting error formatting change:

```diff
-#include <sstream>
@@
-    std::ostringstream MaxNestingDepthError;
-    MaxNestingDepthError << "macros cannot be nested more than "
-                         << MaxNestingDepth << " levels deep."
-                         << " Use -asm-macro-max-nesting-depth to increase "
-                            "this limit.";
-    return TokError(MaxNestingDepthError.str());
+    std::string MaxNestingDepthError;
+    raw_string_ostream OS(MaxNestingDepthError);
+    OS << "macros cannot be nested more than " << MaxNestingDepth
+       << " levels deep."
+       << " Use -asm-macro-max-nesting-depth to increase this limit.";
+    return TokError(OS.str());
```

This keeps LLVM MC string formatting on LLVM's existing raw stream utility
instead of requiring libc++ iostream localization support.
