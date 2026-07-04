# LLD ErrorHandler No-Regex Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::regex` pulls in libc++ locale/collation runtime that is not part of the
minimal SimpleOS sysroot.

Patch `/home/ormastes/llvm-project/lld/Common/ErrorHandler.cpp`:

```diff
+#if !defined(__simpleos__)
 #include <regex>
+#endif
@@
+#if defined(__simpleos__)
+  (void)msg;
+  return std::string(logName);
+#else
   static std::regex regexes[] = {
@@
   return std::string(logName);
+#endif
@@
+#if !defined(__simpleos__)
   if (vsDiagnostics) {
@@
   }
+#endif
```

The regex use is limited to Visual Studio-style diagnostic location rewriting
and duplicate-symbol splitting. SimpleOS keeps normal LLD diagnostics and avoids
linking the unavailable libc++ locale/regex implementation.
