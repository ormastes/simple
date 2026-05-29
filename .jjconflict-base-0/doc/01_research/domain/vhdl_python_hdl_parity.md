# Domain Research: VHDL Python-HDL Parity

Simulation-grade VHDL parity should prioritize deterministic VHDL-2008 output, explicit signed/unsigned conversions through `ieee.numeric_std`, named port maps, conservative reset process templates, and GHDL validation.

Payload enums and inferred RAM templates require representation and vendor-policy decisions. Until those decisions are fully specified, the safer behavior is an early diagnostic rather than emitting non-portable VHDL.
