# Selecting the native linker

The mold-style linker implemented in Simple is an explicit opt-in. It is not
part of automatic hosted linker selection. Normal hosted builds retain the
platform's external linker route; the Unix discovery order is mold, lld, then
system ld, with the existing driver fallback where supported.

Set `SIMPLE_LINKER=internal` for a build to request the Simple implementation.
For example, in PowerShell, set `$env:SIMPLE_LINKER = 'internal'` before invoking
the usual native build command. Remove that process-local override with
`Remove-Item Env:SIMPLE_LINKER` to return to normal external selection. Existing
explicit external linker choices remain available through the same override.
Do not install this override globally merely to make the Simple linker available.

The explicit internal request reaches the native-link facade; it is not an
executable name searched on PATH. Unsupported targets/configuration produce a
named error rather than silently selecting another engine. Target-specific
SimpleOS linking retains its separate explicit-target behavior.

The macOS internal adapter requires explicit `-platform_version macos MIN SDK`
and `--macho-signing-identifier IDENTIFIER` flags in native link configuration.
It accepts `-e ENTRY`, repeated `-rpath PATH`, and
`--macho-max-image-bytes BYTES`; the last is an image-size cap, not a process
memory guarantee. Minimum macOS version is 11.0. Unsupported flags and policies
fail explicitly. The current Mach-O builder requires PIE. Native configuration
with `allow_duplicate_definitions=true` retains the first selected strong
definition; false rejects duplicate strong definitions. Existing direct hosted
and static APIs default to strict rejection. This explicit Simple policy does
not claim equivalence to an Apple linker flag or add weak coalescing. Debug,
stripping, size preference and retained-symbol policies remain unsupported.

Supply actual matching Mach-O objects, archives and thin dylib providers through
explicit library paths. Providers with an `@rpath/` install name also require an
explicit runtime search path such as `-rpath @loader_path`; a library search
directory alone does not supply that runtime path. Explicit `.tbd` files use
the v4 YAML or v5 JSON reader and target selection before provider-graph linking.
Named libraries search each configured directory in `.dylib`, `.tbd`, `.a`
order. A selected stub's error does not fall back to the archive or another
directory. Reexport graphs retain direct-library ordinals and outward alias
names. Use `-syslibroot SDK_DIRECTORY` for an explicit SDK dependency root;
configured library directories are searched first, with dependency `.tbd`
candidates before their binary equivalents. Actual requesting/output directories
resolve `@loader_path`/`@executable_path`; there is no implicit host SDK fallback.
Direct client restrictions use the actual output identity or explicit
`-client_name NAME`, independently of the signing identifier. Indirect providers
do not acquire the executable's direct-client restriction. Unsupported
owner-specific `@rpath`, legacy reexport commands and other SDK semantics still
fail explicitly; this is not complete SDK qualification.
Dyld shared-cache providers remain unsupported, and an SDK version flag does
not discover or admit an SDK. The reader's documented syntax and metadata limits
are in `doc/05_design/compiler/linker/macho_textstub_readers_2026-10-04.md`.
Managed native builds still require their admitted external hosted linker.
This source-level adapter availability does not establish native Darwin execution
or complete macOS support. See the five-host completion matrix for open gates.

Availability is not full qualification. The retained streaming engine and its
logical quotas do not currently satisfy whole-job hard-memory/no-swap admission.
Requests requiring that enforcement continue to return `UnsupportedBudget`.
Source-authored acceptance is distinct from runtime verification; consult the
item4 verification-readiness ledger before claiming a supported release matrix.

Implementation authorities: `src/compiler/70.backend/linker/mold.spl`,
`_LinkerWrapper/native_linking.spl`, and `link_engine_external.spl` in that linker
directory. Existing routing specifications live under
`test/01_unit/compiler/backend/linker/` in `native_linking_internal_spec.spl` and
`link_engine_external_spec.spl`.
