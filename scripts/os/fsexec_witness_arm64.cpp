// SimpleOS in-guest C++ toolchain witness (lane-C1 aarch64, rung R6).
//
// Canonical source. The gate (scripts/qemu/check_simpleos_arm64_clang_compile.shs)
// preprocesses this file ON THE HOST with the lane-C1 cross clang against the
// staged sysroot headers (libc++ v1 + SimpleOS libc), producing the
// self-contained /WITNESS.CPP staged into the guest FAT32 image (the roadmap
// B1 method: the guest FAT32 is root-only 8.3 — the 568-header libc++ closure
// cannot live there; the in-guest cc1 then parses+codegen this real libc++
// translation unit with no #include resolution left to do).
//
// C++17 against libc++ (std::string/std::vector), printf for output (no
// iostreams — less libc++ surface), a class with virtuals, templates.
//
// Compiled -fno-exceptions -fno-rtti: the prebuilt guest libc++ was built
// -fno-exceptions -fno-rtti and, at witness time, libc++abi lacked the
// exception runtime (cxa_exception/cxa_personality) and libc++ emitted no
// RTTI typeinfo objects, so throw/catch is the documented remaining gap
// (lane doc 2026-09-26 R6), not exercised here.
#include <string>
#include <vector>
#include <cstdio>

// A class with virtuals: vtable emission + virtual dispatch.
struct Greeter {
    virtual ~Greeter() {}
    virtual const char *name() const = 0;
    virtual int value() const = 0;
};

struct Adder : Greeter {
    int base;
    explicit Adder(int b) : base(b) {}
    const char *name() const override { return "adder"; }
    int value() const override { return base + 1; }
};

// Templates: instantiated twice.
template <typename T>
T twice(T x) { return x + x; }

static int check(bool ok, const char *what) {
    if (!ok) {
        std::printf("WITNESS_FAIL %s\n", what);
        return 1;
    }
    return 0;
}

// main(int, char**): this toolchain's freestanding C++ emits main with C++
// linkage (clang/lld driver.cpp does the same — see main_shim.S in the
// sysroot build), and the crt0 main shim branches main -> _Z4mainiPPc. A
// no-arg main would mangle to _Z4mainv and never be reached (the R5b
// hollow-green trap).
int main(int argc, char **argv) {
    (void)argc; (void)argv;
    int rc = 0;

    // std::string: heap allocation, SSO, append/compare.
    std::string s = "WITNESS";
    s += "_CXX";
    rc |= check(s == "WITNESS_CXX", "string-eq");
    rc |= check(s.size() == 10u, "string-size");

    // std::vector: growth, iterators, indexing.
    std::vector<int> v;
    for (int i = 0; i < 8; ++i) v.push_back(twice(i));
    rc |= check(v.size() == 8u, "vector-size");
    rc |= check(v[7] == 14, "vector-elem");

    // Virtual dispatch through a base pointer.
    Adder a(41);
    Greeter *g = &a;
    rc |= check(std::string(g->name()) == "adder", "virtual-name");
    rc |= check(g->value() == 42, "virtual-value");

    if (rc == 0) {
        std::printf("WITNESS_CXX_OK\n");
        return 0;
    }
    return 1;
}
