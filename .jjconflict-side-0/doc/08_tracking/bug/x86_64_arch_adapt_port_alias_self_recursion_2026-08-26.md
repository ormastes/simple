# x86_64 architecture adapter port aliases recurse after native lowering

Status: fixed in source; fresh guest capture pending.

The freestanding desktop reached `bga_init_scanout()` and triple-faulted at
`arch_adapt.x86_64.cpu.port_outl`. Disassembly proved all four aliased word/dword
port wrappers called their own entry address. `port_outl` exhausted the stack at
the live PMM/VMM frontier before issuing any PCI configuration instruction.

The adapter now imports the distinctly named, allocation-free
`x86_port_{inw,outw,inl,outl}` functions from the canonical raw port owner. This
removes alias ambiguity and keeps each operation a direct O(1) hardware call.

Diagnostic QEMU evidence after post-load patching reached a valid 3840x1092
scanout, `engine2d-ready`, shell initialization, and `first-frame-rendered`.
That capture is not admissible showcase evidence: Browser Demo returned pid -2,
the WM marked the frame degraded, and the captured bitmap was mostly blank.
