# Canonical Driver Aspect Resolution

This executable unit manual traces `REQ-AF-004`, `REQ-AF-006`, and
`REQ-AF-007` through the real compiler source-resolution facade.

The scenarios verify that compile inputs discover `aspects/__init__.spl`
through `ModuleResolverDiscoveryPort`, the explicit compatibility adapter
returns empty/no-registry state, an aspect importer can resolve a module from
another ordered aspect root, normal business source cannot search or bulk-load
those hidden roots, and the registry fingerprint changes native object-cache
identity. Registry validation errors remain fail-closed and surface from
phase-one as `aspect registry E-...: <manifest path>` before parsing begins.
The composition scenario also verifies that the injected driver retains the
loader adapter while its immutable resolver result remains empty until phase
one invokes discovery.

Executable source:
`test/01_unit/compiler/driver/aspect_registry_driver_resolution_spec.spl`.
