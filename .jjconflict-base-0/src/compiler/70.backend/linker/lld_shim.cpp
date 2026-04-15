// SimpleOS in-process LLD shim.
//
// This file is designed to compile in two modes:
//   - SIMPLE_HAVE_LLD defined: real LLD integration via lld::elf::link.
//   - SIMPLE_HAVE_LLD undefined: stub that returns an error, so the build
//     keeps working until LLD dev headers + libraries are available.
//
// To enable: build clang+lld with LLVM_INSTALL_UTILS=ON, install lld headers,
// then define SIMPLE_HAVE_LLD and link against libLLVM*.a + liblldELF.a etc.

#include "lld_shim.h"
#include <cstring>
#include <cstdio>

#ifdef SIMPLE_HAVE_LLD
#  include "lld/Common/Driver.h"
#  include "llvm/Support/raw_ostream.h"
LLD_HAS_DRIVER(elf)
#endif

extern "C" int simple_lld_elf_link(const char* const* argv,
                                   char* stderr_buf,
                                   int stderr_cap) {
#ifdef SIMPLE_HAVE_LLD
    int argc = 0;
    while (argv && argv[argc]) argc++;

    llvm::ArrayRef<const char*> args(argv, argc);

    std::string err_capture;
    llvm::raw_string_ostream err_stream(err_capture);
    llvm::raw_ostream& err_out = stderr_buf ? err_stream : llvm::errs();

    lld::Result res = lld::lldMain(args, llvm::outs(), err_out,
                                   {{lld::Gnu, &lld::elf::link}});

    if (stderr_buf && stderr_cap > 0) {
        err_stream.flush();
        int n = static_cast<int>(err_capture.size());
        if (n >= stderr_cap) n = stderr_cap - 1;
        std::memcpy(stderr_buf, err_capture.data(), n);
        stderr_buf[n] = '\0';
    }
    return res.retCode;
#else
    const char* msg = "lld_shim: SIMPLE_HAVE_LLD not defined; rebuild with LLD";
    if (stderr_buf && stderr_cap > 0) {
        int n = static_cast<int>(std::strlen(msg));
        if (n >= stderr_cap) n = stderr_cap - 1;
        std::memcpy(stderr_buf, msg, n);
        stderr_buf[n] = '\0';
    }
    (void)argv;
    return 1;
#endif
}
