<!-- codex-research -->
# SimpleOS SMF App Runtime Domain Research

Date: 2026-04-20

## Sources

- ELF gABI, Program Loading and Dynamic Linking:
  https://gabi.xinuos.com/elf/07-loading-intro.html
- ELF gABI, Dynamic Linking:
  https://gabi.xinuos.com/elf/08-dynamic.html
- Linux `dlopen` / `dlmopen` man page:
  https://man7.org/linux/man-pages/man3/dlmopen.3.html
- Linux mount namespaces man page:
  https://www.man7.org/linux/man-pages/man7/mount_namespaces.7.html
- Fuchsia capabilities and namespaces:
  https://fuchsia.dev/fuchsia-src/concepts/components/v2/capabilities
- Apple Dynamic Library Overview:
  https://developer.apple.com/library/archive/documentation/DeveloperTools/Conceptual/DynamicLibraries/100-Articles/OverviewOfDynamicLibraries.html
- WebAssembly Component Model:
  https://github.com/webassembly/component-model
- WebAssembly Component Model Canonical ABI:
  https://component-model.bytecodealliance.org/advanced/canonical-abi.html

## Findings

### Executable format and dynamic linking

The ELF gABI separates file representation from process image creation. Program
headers drive the executable memory image, and dynamic linking completes the
process image by resolving references after load. This maps well to SimpleOS:
keep ELF as the initial process image input and use SMF as the higher-level
container carrying executable bytes, manifests, imports, exports, and hints.

The gABI dynamic section shows the minimum machinery a dynamic linker needs:
dependency records, symbol tables, string tables, relocation tables, init/fini
hooks, and search paths. SimpleOS does not need to clone ELF dynamic linking
fully, but SMF libraries should have equivalent sections or notes.

Linux `dlmopen` adds link-map namespaces for isolation. The useful takeaway for
SimpleOS is that dynamic loading should have an explicit symbol namespace, not a
single global symbol soup. Each process should have a base link namespace, and
plugins can optionally get isolated namespaces later.

Apple's dynamic library documentation emphasizes launch-time footprint and lazy
runtime loading. This supports using SMF libraries for optional app features,
while keeping the first app executable path static and deterministic.

### Filesystem namespaces and capabilities

Linux mount namespaces show that a process-visible mount list is a namespace
boundary. SimpleOS can implement a simpler version first: each process receives
a `NamespaceView` containing root, cwd, mount table view, and capability-limited
service directories.

Fuchsia treats namespace entries and capabilities as the normal way components
discover files and services. This is directly useful for SimpleOS: expose
window, VFS, network, and dynamic-loader services as named namespace endpoints
instead of hardcoded resident calls.

### ABI boundaries

The WebAssembly Component Model's Canonical ABI exists to make independently
built components agree on binary-level data layouts. SimpleOS needs the same
principle for SMF imports/exports and window/VFS IPC payloads: every public
boundary must specify integer widths, string representation, handle ownership,
buffer layout, and versioning.

## Domain Conclusion

The clean design is:

- ELF remains the initial machine process image format.
- SMF becomes the SimpleOS package/container format for apps and libraries.
- LSMF remains the archive format for multiple SMF library modules.
- Dynamic loading uses explicit per-process link namespaces.
- Filesystem namespace and capability namespace become the discovery mechanism
  for apps, libraries, and services.
- Window IPC uses a stable ABI schema, not resident direct calls.

