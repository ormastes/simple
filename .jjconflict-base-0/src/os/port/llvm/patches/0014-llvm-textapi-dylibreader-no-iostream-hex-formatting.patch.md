# LLVM TextAPI DylibReader No-Iostream Hex Formatting Patch

SimpleOS stages libc++ with `_LIBCPP_HAS_LOCALIZATION=0`. Under that config,
`std::stringstream` and iostream manipulators such as `std::setw` are
unavailable.

Patch `/home/ormastes/llvm-project/llvm/lib/TextAPI/BinaryReader/DylibReader.cpp`:

```diff
+#include "llvm/Support/Format.h"
-#include <iomanip>
-#include <sstream>
@@
-      std::stringstream Stream;
+      std::string UUID;
+      raw_string_ostream Stream(UUID);
@@
-        Stream << std::setfill('0') << std::setw(2) << std::uppercase
-               << std::hex << static_cast<int>(UUIDLC.uuid[I]);
+        Stream << format_hex_no_prefix(UUIDLC.uuid[I], 2, true);
```

This keeps Mach-O UUID formatting uppercase and zero-padded without requiring
libc++ iostream localization support.
