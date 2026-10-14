# Provider optional type native regression

Status: **UNRUN**. This manual records required checks, not passing evidence.

Fixture: `test/fixtures/compiler/provider_optional_type_native.spl`.

The fixture calls actual `MirLowering.relocate_provider_default` and uses explicit HirType optional bindings when inspecting its results.

| Case | Required result |
|---|---|
| Array with Some(type) and one literal | Some remains present; integer type, six span fields, and child literal remain correct |
| Empty array with absent type | Type remains absent and elements remain empty |
| Dictionary with concrete key type, Some(value type), and one entry | Both types remain correct; optional value stays present; key/value literals remain correct |
| Empty dictionary with concrete key type and absent value type | Key type remains correct; optional value stays absent |
| Empty dictionary with absent key and value metadata | Both remain absent; existing nil-key guard is preserved |

All cases require zero lowering diagnostics. Assertions exit nonzero; the success marker is emitted only after every case completes:

`provider_optional_type_native=PASS cases=5`

Compile using a coherent admitted self-hosted compiler, exact paired runtime, strict no-stub fallback, and producer/closure-bound cache. Execute the output and retain both exit zero and the success marker. Record compiler hash, source revision, commands, statuses, and artifact identity. Compiler success alone does not execute these assertions.

The old producer's inability to compile the imported MIR closure is a blocker, not a fixture pass. A target-source repair does not change that already-running producer. Do not disable provider defaults, remove metadata, substitute copied implementation code, or retry an unchanged failing closure to obtain a green result. This scalar/optional regression does not claim coverage of provider-local nominal identity remapping or the full Phase3 build.
