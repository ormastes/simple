# Native HIR worker loses declared source roots after closure expansion

Status: source repair proposed; changed-producer qualification pending.

C31 producer `8028c24d93c43300ca53a0e5840d7b2f80d9babe3f217318e3ff0ee36894bf4e`, source `67893d944a326512fd2c3102a9c72ace908f612f`, attempted the separately admitted imported-owner fixture `8b41907c7e8b9c06eb2cbd3dc66d25b6877cdc9d` with normal low-memory ARM and RISC-V builds. The parent selected and parsed four modules. Both HIR children then loaded only main and rejected `lib.dep`, `lib.other`, and `lib.ext`. No MIR or object was produced. Evidence is preserved in C06 `phase3-whole-20261011-c06/c31-native-owner-pair-attempt2`.

The compiled child route is `bootstrap_main`'s internal worker dispatch to `compile_targets.cli_native_build_with_environment_variant_policy_v1`. That route replaces `CompileOptions.input_files` with closure members. `load_sources_impl` previously used that list as the ordered source-root authority. Individual source files cannot resolve an import under its original declared directory root. The separate cause of the child's incomplete initial closure remains under investigation; this change repairs the concrete authority loss and prevents loaded-name shortcuts from bypassing selected owners.

The repair captures effective selectors after the canonical freeze, including default roots and supported argv spellings, using the existing snapshot mapping owner. It carries ordered admitted canonical selectors and their admitted SCV snapshot root independently from source files. Mapping rejects absent snapshots, invalid selectors and missing roots without falling back to closure inputs. Duplicate roots remain ordered. Ambiguity and conflicting preloaded owners fail before an already-loaded shortcut. Existing outer resolver tri-state behavior and source-admission gates remain intact.

Snapshot directory existence is a mapping guard, not admission evidence: provenance comes from the successful canonical freeze before the accessor is called. Native group requests keep their separate admitted group route.

Unit specifications cover the actual admitted accessor, defaults, supported root spellings, option copying, duplicate root order, absent/missing mappings, invalid selectors, ambiguous preloaded owners and owner conflicts. They are prepared, not executed: no qualified actual test runner is yet available. ARM/RV owner regression and canonical runner qualification require a newly constructed producer; source review alone is not acceptance.
