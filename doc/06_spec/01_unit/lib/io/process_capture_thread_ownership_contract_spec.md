# Synchronous capture thread ownership source contract

Status: Simple SSpec NOT_RUN. These source assertions check that descriptor/result
ownership, destructor wiring and scalar metrics retention remain connected to the
actual runtime owner. They are source checks, not concurrency behavior proof.

The independent production-owner native witness ran once on Linux and passed 41
checks. See the dated capture-admission report for exact commands and bounds.
No Windows or Simple runtime result is inferred from that focused native result.
