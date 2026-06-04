# Local Research: VHDL Python-HDL Parity

Existing implementation already contains structured VHDL metadata types, MIR VHDL process instructions, fixed-width primitive mappings, tuple return ABI support, source-facade coverage for clocked processes and tuple bundles, and a VHDL constraint checker.

The main remaining risks are broad HLS-style features: general helper subprogram emission, ROM/RAM inference, payload enum tagged records, and full testbench conversion. This pass keeps those as explicit diagnostics or documented deferrals unless the current MIR/source facade already has enough structure to lower safely.
