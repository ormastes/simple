# doc/06_spec/ Manifest

Specification documentation. Contains both **generated** and **manually written** specs.

## Generated vs Manual

| Discriminator | Generated | Manual |
|---------------|-----------|--------|
| Suffix | Always `*_spec.md` | Any name (README, INDEX, CATALOG, guides) |
| Header | Contains `_Generated from \`<source>\`_` | No generation header |
| Lifecycle | Overwritten by `bin/simple spec-gen` | Hand-edited, survives regeneration |
| Location | Current SPipe docs mirror numbered test roots such as `{kind}/{domain}/{subdomain}/name_spec.md` | Same tree, non-`_spec.md` names |

**Generators:**
- `bin/simple spec-gen [path]` — extracts doc from `*_spec.spl` test files (`src/app/spec_gen/main.spl`)
- Test runner — `feature.md`, `pending_feature.md` regenerated every test run
- `src/app/doc/gen_spec_docs.spl` — README, SPEC_CATALOG, MIXIN_FEATURES

## Directory Structure

| Entry | Description |
|---|---|
| `00_formal_verification/` | Formal-verification specs |
| `01_unit/` | Unit specs (mirrors `test/01_unit/`) |
| `01_unit/app/` | Application unit specs (cli, mcp, rtl, tooling, ui) |
| `01_unit/browser_engine/` | Browser engine unit specs |
| `01_unit/compiler/` | Compiler unit specs (backend, codegen, mir, parser, semantics) |
| `01_unit/lib/` | Library unit specs |
| `01_unit/os/` | OS unit specs |
| `02_integration/` | Integration specs (mirrors `test/02_integration/`) |
| `02_integration/app/` | Application integration specs |
| `02_integration/remote_jit/` | Remote JIT integration specs |
| `02_integration/rendering/` | Rendering integration specs |
| `03_system/` | System specs (mirrors `test/03_system/`) |
| `03_system/app/` | Application system specs (browser, compiler, dap, ide, mcp, ui) |
| `03_system/compiler/` | Compiler system specs |
| `03_system/os/` | OS system specs |
| `03_system/hardware/` | Hardware system specs |
| `03_system/gui/` | GUI/UI system specs |
| `03_system/infrastructure/` | Infrastructure system specs |
| `05_perf/` | Performance specs (mirrors `test/05_perf/`) |
| `05_perf/graphics_2d/` | 2D graphics performance specs |
| `feature/` | Legacy/manual feature specs |
| `unit/` | Legacy/manual unit specs |
| `integration/` | Legacy/manual integration specs |
| `system/` | Legacy/manual system specs |
| `perf/` | Legacy/manual performance specs |
| `feature.md` | Feature list (auto-generated every test run) |
| `pending_feature.md` | Pending features (auto-generated every test run) |
| `feature_db.sdn` | Feature database |
| `bootstrap_test_gate.sdn` | Bootstrap test gate config |
| `INDEX.md` | Spec index |
| `README.md` | Overview |
| `FILE.md` | This manifest |

## Rules

- Generated `*_spec.md` files must NOT be hand-edited (they get overwritten)
- Manual specs use non-`_spec.md` names or live in dirs without a corresponding test
- Spec path mirrors test path: `test/01_unit/compiler/parser/x_spec.spl` -> `doc/06_spec/01_unit/compiler/parser/x_spec.md`
