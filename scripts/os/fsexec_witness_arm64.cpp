// SimpleOS in-guest C++ witness (lane-C1 aarch64, rungs R6a/R6b/R6c).
//
// LEANEST possible C++ TU — self-contained, NO #includes, NO STL. Proves the
// in-guest C++ frontend + link + run with the minimum AST: one virtual base
// class (vtable emission + dynamic dispatch), operator new/delete (libc++abi
// runtime), and printf. std::string/std::vector/iostreams are deliberately
// absent: their libc++ header closure is what made the earlier witness a
// ~10 MiB AST/PCH that the guest cc1 could not read inside the boot budget
// under TCG (agent-47, run-20260927_024414). This file compiles in ~seconds.
//
// The virtual + new + delete still pull the minimal libc++abi runtime at
// LINK time (rung R6b: operator new/delete, the vtable's key function) — that
// is the C++ proof. Compiled -fno-rtti (matches the prebuilt guest libc++;
// the fork's cc1 compiles exceptions OUT by default and REJECTS an explicit
// -fno-exceptions, so no such flag is passed — the guest R6a cc1 line omits
// it). throw/catch remains the documented gap and is not exercised.
//
// main(int, char**): this toolchain's freestanding C++ emits main with C++
// linkage (the crt0 main shim branches main -> _Z4mainiPPc); a no-arg main
// would mangle to _Z4mainv and never be reached (the R5b hollow-green trap).
// The product prints WITNESS_CXX_42 (b->value() == 42 through the virtual).

struct Base {
    virtual ~Base() {}
    virtual int value() const { return 1; }
};

struct Derived : Base {
    int value() const override { return 42; }
};

extern "C" int printf(const char *fmt, ...);

int main(int argc, char **argv) {
    (void)argc; (void)argv;
    Base *b = new Derived();
    printf("WITNESS_CXX_%d\n", b->value());
    delete b;
    return 0;
}
