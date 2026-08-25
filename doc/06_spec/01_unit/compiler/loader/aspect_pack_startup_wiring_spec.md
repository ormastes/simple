# Aspect-pack CLI startup wiring

Mirror of `test/01_unit/compiler/loader/aspect_pack_startup_wiring_spec.spl`.

The executable spec proves that startup pack lists are parsed, real pack files
are read and registered, malformed or missing requested packs fail closed, and
the Pure Simple CLI retains the product call site.

It also pins the startup fast-path boundary: `--help`/`-h` and `--version`/`-v`
dispatch precedes all aspect-pack environment/file IO and loader allocation.
A commandless invocation enters the executable REPL, so it and explicit
commands in the ordinary post-filter dispatch chain retain the same fail-closed
startup hop. Earlier dedicated app and native-build dispatches keep their
pre-existing owners and are outside this focused wiring contract.

The source-order assertions cover CLI wiring because importing and invoking
the complete CLI graph is not supported by this focused unit-spec fixture.
