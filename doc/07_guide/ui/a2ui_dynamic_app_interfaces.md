# Developer & Operator Guide: A2UI and Dynamic App Interfaces

**Design Doc:** [a2ui_dynamic_app_interfaces.md](../../05_design/a2ui_dynamic_app_interfaces.md)

## 1. Architecture Summary

- **Screens (`*.screen.sdn`)**: Single anonymous root strict-SDN table with columns `|id, parent, slot, order, region, repeat, key, expression|`. Each `expression` cell is parsed once by `a2ui_parse_express_constructor` using the shared scalar VM.
- **App Interfaces (`*.interface.sdn` / `AppInterfaceRegistry`)**: Trusted registration of semantic resources, bounded queries, typed commands, and draft contracts (`writable_paths` vs `protected_paths`).
- **Authority (`*.authority.sdn` / `AuthorityGate`)**: Separate default-deny policy defining region hierarchies/ceilings, field-level use/release rules, and HMAC-SHA256 capability grants.
- **Hot Swap vs Dynamic UI Composition**:
  - Use `runtime.admit_screen_composition(...)` or `CaretA2uiHost.update_screen_dynamically(...)` to change panels, bindings, and admitted forms without changing executable code (`code_generation` unchanged).
  - Use `HandlerGenerationOwner.hot_swap_generation(abi_tag)` or `CaretA2uiHost.hot_swap_handler(...)` when handler implementation code changes. It delegates execution leases and quiescence/reclamation to `std.common.aspect_dynload_lifecycle_v1` while preserving active surfaces, drafts, and session state.

## 2. Running Caret Suite with A2UI

- Summary output: `caret --a2ui` (or `CARET_SUITE_MODE=a2ui`)
- Standard A2UI v1.0 wire JSON output (`sendDataModel: false`): `caret --a2ui-json`
- Interactive TUI inspection command: `/a2ui` inside `cs_run` / `cs_run_live`

## 3. Native Verification Harness

Compile and run the full native verification suite using the Stage 2 pure-Simple compiler:

```sh
PATH="/home/yoon/dev/llvm/install/bin:$PATH" SIMPLE_LIB=src \
  /path/to/simple native-build --backend=cranelift \
  --source src/lib --source src/app --source src/os --source test/fixtures \
  --entry-closure --entry test/fixtures/a2ui_native_verify.spl \
  --output /tmp/a2ui_native_verify_bin && /tmp/a2ui_native_verify_bin
```
