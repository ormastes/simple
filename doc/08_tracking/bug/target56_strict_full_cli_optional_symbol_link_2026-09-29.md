# Target 5/6 strict full CLI optional-symbol link boundary

Status: open. The development `main` source at `9d09842c404` did not
produce a no-stub full CLI executable on Linux ARM64.

The pure-Simple Stage2 producer (SHA-256
`5d71c26b371b83d0041e10b815dae153a38b9f7c61aa0931f3473aaee919e2f6`)
compiled `src/app/cli/main.spl` with `--source src/compiler --source src/app
--source src/lib --entry-closure --backend cranelift --mode dynload` and
`SIMPLE_NO_STUB_FALLBACK=1`. One phase- and entry-bound cache was retained
across three bounded attempts (180, 300, and 180 seconds). The first two
limits left 653 and 2,281 cached objects. The third reached native link with
`compiled=204 reused=2281 failed=0`; no Simple source compilation error was
reported. `mold` then rejected 163 distinct unresolved symbols, including
CUDA, Vulkan, SDL, SQLite, hosted artifact, and core array helpers. No full
CLI binary was produced.

This is a full-closure/link admission failure, not evidence for the optional
provider size or startup gates. The focused CAS native fixture on the same
source passes with no stub fallback, so its narrow result remains separate.

Next repair: classify each unresolved symbol against the core runtime owner
and optional provider manifest. Keep no-import and CLI startup paths free of
eager optional provider references; route first demand through admitted
providers or supply a proven core owner. Rebuild once with the same cache and
strict no-stub setting, then measure full CLI size, startup, RSS, and the
provider trace. Do not substitute generated stubs or a Rust seed.
