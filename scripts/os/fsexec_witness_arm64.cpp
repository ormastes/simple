// SimpleOS in-guest C++ witness (lane-C1 aarch64, rungs R6a/R6b/R6c).
//
// Canonical source. MINIMAL TU (~1.5 KB): the guest FAT32 is root-only 8.3, so
// the 187-header libc++ tree cannot live there, and host-preprocessing the
// <string>/<vector>/<cstdio> closure into the TU (the old roadmap-B1 method)
// produced a ~1.8 MiB WITNESS.CPP that the guest cc1 could not parse inside
// the boot budget under TCG (lane doc 2026-09-26, agent-46 throughput wall).
//
// Instead the gate builds /CXX.PCH ON THE HOST with the same cross clang-20
// (a precompiled header carrying <string>, <vector>, <cstdio>), and the guest
// cc1 runs with `-include-pch /CXX.PCH`: it deserializes the AST instead of
// lexing/parsing the header text, then parses+codegens only this file.
// The guest cc1 reads the PCH through the FileManager stream path (the fd-mode
// fstat S_IFIFO fix), so the anonymous-only guest mmap is never involved.
//
// This file therefore carries NO #include lines — every declaration comes from
// the PCH. Covers: a class with virtuals (vtable emission + dispatch),
// std::string (SSO + append + compare), std::vector (growth + indexing), a
// template function instantiated twice, printf output. -fno-exceptions
// -fno-rtti matches the prebuilt guest libc++; throw/catch remains the
// documented gap and is not exercised.
//
// main(int, char**): this toolchain's freestanding C++ emits main with C++
// linkage (the crt0 main shim branches main -> _Z4mainiPPc, same convention as
// the clang/lld drivers); a no-arg main would mangle to _Z4mainv and never be
// reached (the R5b hollow-green trap).

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

// Templates: instantiated for int and for long.
template <typename T>
T twice(T x) { return x + x; }

static int check(bool ok, const char *what) {
    if (!ok) {
        std::printf("WITNESS_FAIL %s\n", what);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    (void)argc; (void)argv;
    int rc = 0;

    // std::string: SSO storage, append, compare, c_str (stays inside libc++'s
    // 22-byte SSO buffer — no heap traffic).
    std::string s = "WITNESS";
    s += "_CXX";
    rc |= check(s == "WITNESS_CXX", "string-eq");
    rc |= check(s.size() == 10u, "string-size");

    // std::vector: heap growth, indexing, iterators.
    std::vector<int> v;
    for (int i = 0; i < 8; ++i) v.push_back(twice(i));
    rc |= check(v.size() == 8u, "vector-size");
    rc |= check(v[7] == 14, "vector-elem");
    rc |= check(twice(21L) == 42L, "template-long");

    // Virtual dispatch through a base pointer.
    Adder a(41);
    Greeter *g = &a;
    rc |= check(std::string(g->name()) == "adder", "virtual-name");
    rc |= check(g->value() == 42, "virtual-value");

    if (rc == 0) {
        std::printf("WITNESS_CXX_OK %s %d\n", s.c_str(), v[7]);
        return 0;
    }
    return 1;
}
