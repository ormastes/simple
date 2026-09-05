# LLVM Instrumentation No-Iostream Hex Formatting Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::stringstream`, `std::ostringstream`, and iomanip helpers such as
`std::hex`, `std::setw`, and `std::setfill` are unavailable.

Patch:

- `/home/ormastes/llvm-project/llvm/lib/Transforms/Instrumentation/InstrOrderFile.cpp`
- `/home/ormastes/llvm-project/llvm/lib/Transforms/Instrumentation/AddressSanitizer.cpp`

Replace iostream hex formatting with LLVM's existing `utohexstr`:

```diff
-        std::stringstream stream;
-        stream << std::hex << MD5Hash(F.getName());
-        std::string singleLine = "MD5 " + stream.str() + " " +
+        std::string singleLine = "MD5 " +
+                                 utohexstr(MD5Hash(F.getName()), true) + " " +
                                  std::string(F.getName()) + '\n';
@@
-    std::ostringstream Name;
-    Name << kAsanSetShadowPrefix;
-    Name << std::setw(2) << std::setfill('0') << std::hex << Val;
+    std::string Name =
+        std::string(kAsanSetShadowPrefix) + utohexstr(Val, true, 2);
```

This keeps formatting local and avoids growing libc++ iostream/localization
support just for hex strings.
