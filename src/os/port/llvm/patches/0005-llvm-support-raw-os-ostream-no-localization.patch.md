# 0005 - `raw_os_ostream` no-localization libc++ guard

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. In that mode libc++
intentionally leaves `std::basic_ostream` incomplete, so LLVM Support's
`raw_os_ostream.cpp` cannot instantiate `std::ostream::write()` or
`std::ostream::tellp()`.

Keep the no-localization cross build moving by making the adapter a no-op when
libc++ exposes that configuration. This is a compile-enabling cross-build
patch; full iostream behavior requires enabling libc++ localization later.

Target file:

`llvm/lib/Support/raw_os_ostream.cpp`

Hunk:

```cpp
void raw_os_ostream::write_impl(const char *Ptr, size_t Size) {
+#if defined(_LIBCPP_HAS_LOCALIZATION) && !_LIBCPP_HAS_LOCALIZATION
+  (void)Ptr;
+  (void)Size;
+#else
   OS.write(Ptr, Size);
+#endif
 }

-uint64_t raw_os_ostream::current_pos() const { return OS.tellp(); }
+uint64_t raw_os_ostream::current_pos() const {
+#if defined(_LIBCPP_HAS_LOCALIZATION) && !_LIBCPP_HAS_LOCALIZATION
+  return 0;
+#else
+  return OS.tellp();
+#endif
+}
```
