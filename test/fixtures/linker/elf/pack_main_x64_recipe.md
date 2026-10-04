# Mapped-provider hosted fixture

`pack_main_x64.c` defines a hosted C `main` returning 42, without Simple runtime
symbols. Built in WSL Ubuntu using clang; ELF inspection confirms machine x86-64,
ET_REL, and a global 18-byte `main` definition.

```text
clang --target=x86_64-unknown-linux-gnu -O0 -fPIE -fno-stack-protector -fno-unwind-tables -fno-asynchronous-unwind-tables -c pack_main_x64.c -o pack_main_x64.o
```

Object construction is fixture evidence only. No Simple provider, linked image,
or SSpec was built or executed during authoring.
