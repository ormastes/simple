# Host CPU Runtime Variants Agent Tasks

1. Add a shared host CPU config subsystem in `simple-simd`.
2. Switch compiler and runtime dispatch consumers to the new active tier.
3. Extend native loader runtime library probing for suffixed sibling variants.
4. Extend package metadata and embedded-runtime selection for multi-variant payloads.
5. Add focused unit coverage for config clamping, tier precedence, loader probing, and manifest round-trips.

