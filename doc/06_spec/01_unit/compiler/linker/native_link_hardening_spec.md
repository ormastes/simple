# Native linker hardening

Mirror of `test/01_unit/compiler/linker/native_link_hardening_spec.spl`.

The executable SSpec checks strong Vulkan provider detection, archive-root rendering across linker families, preservation of fallback objects, platform-correct unresolved-symbol policy, strict-link and flight-closure behavior, complete CRT endpoints, configured prefixes, canonical native-all selection, hosted dependencies, and use of the shared policy across native/shared paths.

These are focused policy assertions; they do not perform a complete link on every supported host.
