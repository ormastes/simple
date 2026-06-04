# doc/06_spec/ Manifest

Specification documentation. Contains both **generated** and **manually written** specs.

## Generated vs Manual

| Discriminator | Generated | Manual |
|---------------|-----------|--------|
| Suffix | Always `*_spec.md` | Any name (README, INDEX, CATALOG, guides) |
| Header | Contains `_Generated from \`<source>\`_` | No generation header |
| Lifecycle | Overwritten by `bin/simple spec-gen` | Hand-edited, survives regeneration |
| Location | Mirrors test path: `{category}/{domain}/{subdomain}/name_spec.md` | Same tree, non-`_spec.md` names |

**Generators:**
- `bin/simple spec-gen [path]` — extracts doc from `*_spec.spl` test files (`src/app/spec_gen/main.spl`)
- Test runner — `feature.md`, `pending_feature.md` regenerated every test run
- `src/app/doc/gen_spec_docs.spl` — README, SPEC_CATALOG, MIXIN_FEATURES

## Directory Structure (max 4 levels: category/domain/subdomain/file)

| Entry | Description |
|---|---|
| `unit/` | Unit-level specs (mirrors `test/01_unit/`) |
| `unit/app/` | Application unit specs (cli, mcp, rtl, tooling, ui) |
| `unit/browser_engine/` | Browser engine unit specs |
| `unit/compiler/` | Compiler unit specs (backend, codegen, mir, parser, semantics) |
| `unit/hardware/` | Hardware unit specs (qor, rv32i_rtl) |
| `unit/lib/` | Library unit specs (common, crypto, browser_engine, skia, std) |
| `unit/os/` | OS unit specs (kernel, drivers, desktop, services) |
| `integration/` | Integration specs (mirrors `test/02_integration/`) |
| `integration/app/` | Application integration specs |
| `integration/remote_jit/` | Remote JIT integration specs |
| `integration/rendering/` | Rendering integration specs |
| `system/` | System-level specs (mirrors `test/03_system/`) |
| `system/app/` | Application system specs (browser, compiler, dap, ide, mcp, ui) |
| `system/compiler/` | Compiler system specs (modules: gpu_simd, grammar, parser, etc.) |
| `system/os/` | OS system specs (baremetal, kernel, storage) |
| `system/hardware/` | Hardware system specs (riscv64_fpga) |
| `system/gui/` | GUI/UI system specs |
| `system/infrastructure/` | Infrastructure system specs |
| `feature/` | Language feature specs |
| `feature/language/` | Core language feature specs |
| `feature/usage/` | Usage pattern specs (252 specs) |
| `feature/app/` | Application feature specs (remote_baremetal, remote_jit, web_dashboard) |
| `perf/` | Performance specs |
| `perf/graphics_2d/` | 2D graphics performance specs |
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
- Spec path mirrors test path: `test/01_unit/compiler/parser/x_spec.spl` -> `doc/06_spec/unit/compiler/parser/x_spec.md`
- Maximum 4 levels under `doc/06_spec/` (category/domain/subdomain/file)
