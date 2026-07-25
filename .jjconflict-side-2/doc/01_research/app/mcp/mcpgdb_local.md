# mcpgdb Domain Research

External references used:
- OpenOCD remote GDB flow: https://openocd.org/doc/html/GDB-and-OpenOCD.html
- GDB interpreters and MI/CLI split: https://sourceware.org/gdb/current/onlinedocs/gdb.html/Interpreters.html
- clangd compile command design: https://clangd.llvm.org/design/compile-commands
- clangd indexing/background behavior: https://clangd.llvm.org/design/indexing.html
- LLDB public API and debugger concepts: https://lldb.llvm.org/python_api.html
- TRACE32 GDB backend documentation: https://www2.lauterbach.com/pdf/backend_gdb.pdf

Key conclusions:
- OpenOCD and TRACE32 are reasonable to model as remote-GDB transports inside a common debugger abstraction.
- clangd should remain workspace-scoped rather than tied to one debug session.
- Raw command passthrough needs explicit allow/block rules because debugger CLIs expose shell, scripting, and target-mutation paths.
