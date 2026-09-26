// PCH source header for the lane-C1 aarch64 in-guest C++ witness (R6a).
//
// The gate (scripts/qemu/check_simpleos_arm64_clang_compile.shs) compiles this
// header ON THE HOST with the lane-C1 cross clang-20 into /CXX.PCH (cc1
// -emit-pch, flags identical to the guest R6a cc1 line), and the guest cc1
// loads it with `-include-pch /CXX.PCH` so the libc++ declarations below are
// deserialized as a precompiled AST instead of re-parsed from ~1.8 MiB of
// header text in-guest (the agent-46 throughput wall).
//
// Keep this list MINIMAL: every header here is AST the guest cc1 deserializes.
#include <string>
#include <vector>
#include <cstdio>
