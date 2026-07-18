# LLVM AArch64 no-sstream frame helper patch

The SimpleOS libc++ config keeps localization disabled and does not provide the
full iostream/sstream runtime surface. The AArch64 backend used
`std::ostringstream` only as a local string builder for outlined frame helper
names.

Patch `llvm/lib/Target/AArch64/AArch64LowerHomogeneousPrologEpilog.cpp` to use
LLVM's raw stream helper instead:

```cpp
#include "llvm/Support/raw_ostream.h"

std::string RegName;
raw_string_ostream RegStream(RegName);
...
return RegStream.str();
```

This preserves the generated helper names without pulling in libc++ sstream.
