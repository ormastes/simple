# Native Binary Strip Contract

The native build pipeline must carry the public `--strip` request from the CLI
through `CompileOptions`, `NativeLinkOptions`, and `NativeLinkConfig`. Darwin
links retain `dead_strip` and add `-S -x`; ELF links retain section garbage
collection and add `--strip-all`. The unstripped path remains unchanged.

This contract does not permit unresolved-symbol stubs or relax undefined-symbol
handling. A real before/after binary-size receipt remains blocked until a newly
built, producer-authenticated pure-Simple compiler contains this source change;
the currently admitted binary predates it and cannot measure the implementation.
