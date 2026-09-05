# Pure Simple provider host proof needs an admitted runtime capsule link

Status: open.

The admitted Stage 2 compiler produced a 37 KB Pure Simple provider archive
and a host shared object with the exact two provider ABI symbols. Loading and
executing that provider requires the host process to export the runtime
services used by its codec closure.

Adding `--export-dynamic` to a selfcheck linked from monolithic
`runtime_native.c` is unsound: it defeats section garbage collection and pulls
unresolved runtime owners such as `spl_strdup`, `spl_panic`, process services,
and SIMD probes into the link.

Required fix: the provider integration gate must link the admitted, complete
runtime capsule plus its recorded dependency/link manifest, then export only
the provider-required runtime surface. It must not guess dependency archives
or weaken unresolved-symbol checks. Until that owner contract exists, the
verified evidence is archive production and exact symbol export, not full
Pure-Simple provider execution.
