# Processing Metal MSL Operator Guide

Generate and validate an artifact without probing Metal hardware on any host.
On macOS with Xcode command-line tools and a Metal device, retain the exact MSL,
compile it with `xcrun -sdk macosx metal` and `xcrun -sdk macosx metallib`, then
run the prepared SPipe scenario.  Admission requires a positive stable device
identity, nonzero backend handle, raw device readback, exact CPU-oracle parity,
and no fallback.

Cache keys cover IR semantics, target, entry point, ABI and generator versions;
change in any field invalidates cached source/library material.  Startup probes
capability once.  Hot requests do not scan the tree or spawn compilers after a
cache hit.  Budgets are generation <10 ms/8 MiB and warm lookup <1 ms; record
native cold compile, dispatch latency, and max RSS separately.

Linux cannot admit the native Metal row.  Use the exact resume command and
retained-artifact list in the authoritative Metal TODO.
