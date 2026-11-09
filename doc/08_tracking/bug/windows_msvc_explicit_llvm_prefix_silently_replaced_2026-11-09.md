# Explicit MSVC LLVM prefix silently replaced during setup

- Status: fix implemented; focused shell regression passed; full MSVC bootstrap blocked
- Source base: `8af0292ee8ad`
- Owner: `scripts/setup/windows-msvc-bootstrap-env.shs`

When `LLVM_SYS_231_PREFIX` or `SIMPLE_LLVM_WIN_ROOT_23` named a prefix without
`bin/clang-cl.exe`, setup searched the automatic candidates and silently
selected another compiler. This contradicted the selection block's documented
contract: discovery applies only when the caller supplied no prefix.

The repair restricts automatic discovery to callers with neither prefix set.
The existing missing-compiler failure now rejects invalid explicit selections.
`LLVM_SYS_231_PREFIX` retains precedence over `SIMPLE_LLVM_WIN_ROOT_23`.

The production-block shell fixture reproduced the failure before the repair:
an invalid primary prefix selected the fixture's local-store compiler and
reported success. After the repair, seven cases pass: valid primary precedence,
alternate selection, primary-only selection, missing primary rejection, missing
alternate rejection, missing-primary/valid-alternate rejection, and unpinned
automatic discovery. The existing Windows toolchain contract invokes this
fixture. These checks prove shell selection only, not compiler admission.

## Host diagnostic and remaining bootstrap inputs

Installed LLVM `23.1.5` targets `x86_64-pc-windows-msvc`. Its `clang-cl.exe`
compiled a header-free C entry object with `/Zl`; `lld-link.exe` linked it with
`/entry:main /subsystem:console /nodefaultlib /machine:x64`. The executable
returned the expected `42`. This demonstrates runnable MSVC-ABI COFF tool
output; it is not a Simple compiler or a full-runtime Hello qualification.

A separate `#include <stdio.h>` compile fails with `stdio.h file not found`.
Visual Studio VC tools discovery (`vswhere.exe`), VC headers/libraries and the
Windows SDK remain missing on this host. The installed LLVM package also has
no `llvm-config.exe`; LLVM-enabled Rust-seed bootstrap requires a complete
development distribution, not only the Clang tools. No GNU substitution,
installer restart, self-hosted runtime PASS or completed bootstrap is claimed.
