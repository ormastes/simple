# Aspect-pack CLI startup wiring

Mirror of `test/01_unit/compiler/loader/aspect_pack_startup_wiring_spec.spl`.

The executable spec proves that startup pack lists are parsed, real pack files
are read and registered, malformed or missing requested packs fail closed, and
the Pure Simple CLI retains the product call site.

Multi-pack registration is atomic at the startup boundary. If a later missing,
malformed, or duplicate path fails, packs accepted earlier in that invocation
are unregistered in reverse order and successful cleanup reports zero packs.
The missing-second and duplicate-second scenarios prove cleanup by successfully
registering the first path again on the same diagnostic handle. If cleanup is
ever refused, the original load error remains first and rollback diagnostics
are appended so the startup failure becomes louder rather than being hidden;
`packs_loaded` then truthfully reports registrations that cleanup retained.

It also pins the startup fast-path boundary: `--help`/`-h` and `--version`/`-v`
dispatch precedes all aspect-pack environment/file IO and loader allocation.
A commandless invocation enters the executable REPL, so it and explicit
commands in the ordinary post-filter dispatch chain retain the same fail-closed
startup hop. Earlier dedicated app and native-build dispatches keep their
pre-existing owners and are outside this focused wiring contract.

The source-order assertions cover CLI wiring because importing and invoking
the complete CLI graph is not supported by this focused unit-spec fixture.
The returned loader handle supports focused assertions and diagnostics only;
the production startup caller discards it, so this does not claim a useful
persistent loader service.
