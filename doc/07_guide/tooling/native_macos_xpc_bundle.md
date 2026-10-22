# Native macOS XPC bundle generator

`src/app/macos_xpc_bundle/main.spl` packages two prebuilt native Mac Mach-O
executables into a signed app with an embedded App Sandbox XPC service. It runs
on the Mac host; there is no VM or guest image.

```sh
bin/simple run src/app/macos_xpc_bundle/main.spl bundle \
  /absolute/path/to/SimpleHost \
  /absolute/path/to/SimpleWorker \
  org.simple.NativeHost org.simple.NativeWorker -
```

The final argument is `-` for local ad-hoc signing or a 40-digit certificate
SHA-1 for a keychain signing identity. The command prints the private staged
`SimpleHost.app` path. It never replaces an existing destination. It checks
Mach-O executable type, writes and lints app/XPC property lists, marks both
executables runnable, signs the service before the app, and verifies both
signatures. Supply self-contained executables; external libraries and resources
are not copied into the bundle.

The host executable must connect to the service bundle identifier, and the
service executable must enter `xpc_main`. The generator supplies neither
entrypoint. A successful command proves bundle construction and code-signing
verification only. Launch the app and verify actual XPC startup, sandbox
state, filesystem denial, exit identity, and descendant cleanup on an
authorized unrestricted Mac before advertising Simple Container support.

The focused Simple spec is
`test/01_unit/app/macos_xpc_bundle/generator_spec.spl`. It was written but
not run in the 2026-09-28 logical session because that session exhausted the
repository's verify/fix cap. A host-only experiment signed an app containing
copies of `/usr/bin/true` with the same ad-hoc nested signing order and strict
verification; it did not launch an XPC service.
