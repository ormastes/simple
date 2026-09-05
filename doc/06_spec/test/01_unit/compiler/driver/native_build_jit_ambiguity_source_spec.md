# Native Build Jit Ambiguity Source Specification

> <details>

<!-- sdn-diagram:id=native_build_jit_ambiguity_source_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_build_jit_ambiguity_source_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_build_jit_ambiguity_source_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_build_jit_ambiguity_source_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Jit Ambiguity Source Specification

## Scenarios

### native-build JIT ambiguity source guards

#### keeps template instantiation progress tracking off Set mutation assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/40.mono/instantiation.spl")
expect(src).to_contain("in_progress: [text]")
expect(src).to_contain("self.in_progress = self.in_progress.push(key)")
expect(src).to_contain("_template_remove_text(self.in_progress, key)")
expect(src.contains("in_progress: Set<text>")).to_equal(false)
expect(src.contains("self.in_progress = self.in_progress.insert(key)")).to_equal(false)
expect(src.contains("self.in_progress = self.in_progress.remove(key)")).to_equal(false)
```

</details>

#### keeps lazy linker instantiation progress tracking off Set mutation assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/70.backend/linker/lazy_instantiator.spl")
expect(src).to_contain("in_progress: [text]")
expect(src).to_contain("self.in_progress = self.in_progress.push(symbol)")
expect(src).to_contain("_lazy_remove_text(self.in_progress, symbol)")
expect(src.contains("in_progress: Set<text>")).to_equal(false)
expect(src.contains("self.in_progress = self.in_progress.insert(symbol)")).to_equal(false)
expect(src.contains("self.in_progress = self.in_progress.remove(symbol)")).to_equal(false)
```

</details>

#### keeps linker symbol collection and unresolved tracking receiver-explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/70.backend/linker/link.spl")
expect(src).to_contain("unresolved: [text]")
expect(src).to_contain("val smf_reader: SmfReaderImpl = reader")
expect(src).to_contain("for symbol in smf_reader.exported_symbols():")
expect(src).to_contain("not self.unresolved.contains(symbol.name)")
expect(src).to_contain("self.unresolved = self.unresolved.push(symbol.name)")
expect(src.contains("unresolved: Set<text>")).to_equal(false)
expect(src.contains("for symbol in reader.exported_symbols():")).to_equal(false)
expect(src.contains("\n                        self.unresolved.push(symbol.name)")).to_equal(false)
```

</details>

#### removes the dead generic backend run_module ambiguity surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/80.driver/driver.spl")
expect(src.contains("fn run_module(backend: Backend, module: HirModule)")).to_equal(false)
expect(src.contains("backend.process_module(module)")).to_equal(false)
```

</details>

#### keeps SFFI process spec generation off the generic process_module name

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workspace_src = file_read("src/compiler/90.tools/sffi_gen/sffi_gen_workspace.spl")
val process_src = file_read("src/compiler/90.tools/sffi_gen/specs/process_mod.spl")
val init_src = file_read("src/compiler/90.tools/sffi_gen/specs/__init__.spl")
expect(workspace_src).to_contain("sffi_process_module()")
expect(process_src).to_contain("fn sffi_process_module() -> ModuleSpec:")
expect(init_src).to_contain("export sffi_process_module")
expect(workspace_src.contains("process_module()")).to_equal(false)
expect(process_src.contains("fn process_module() -> ModuleSpec:")).to_equal(false)
```

</details>

#### keeps VHDL codegen helpers off ambiguous array push calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/80.driver/driver_compile_vhdl_codegen.spl")
expect(src).to_contain("body_lines = body_lines + [raw_line]")
expect(src).to_contain("ports = ports + [clock_port]")
expect(src).to_contain("sanitized = sanitized + [port_name]")
expect(src.contains("body_lines = body_lines.push(raw_line)")).to_equal(false)
expect(src.contains("ports = ports.push(clock_port)")).to_equal(false)
expect(src.contains("ports = ports.push(\"        ")).to_equal(false)
expect(src.contains("sanitized = sanitized.push(port_name)")).to_equal(false)
```

</details>

#### keeps EffectEnv dirty tracking off Set insert and clear

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/compiler/00.common/effects.spl")
expect(src).to_contain("dirty: [Symbol]")
expect(src).to_contain("_effect_symbol_append_unique(self.dirty, sym)")
expect(src).to_contain("self.dirty = []")
expect(src.contains("dirty: Set<Symbol>")).to_equal(false)
expect(src.contains("self.dirty.insert(sym)")).to_equal(false)
expect(src.contains("self.dirty.clear()")).to_equal(false)
```

</details>

#### passes native-build driver inputs through fixed bootstrap slots

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_src = file_read("src/app/io/_CliCompile/compile_targets.spl")
val driver_src = file_read("src/compiler/80.driver/driver.spl")
expect(cli_src).to_contain("fn cli_native_build_add_bootstrap_input")
expect(cli_src).to_contain("options = cli_native_build_add_bootstrap_input(options, cf)")
expect(cli_src).to_contain("options = cli_native_build_add_bootstrap_input(options, source_dir)")
expect(cli_src).to_contain("options = cli_native_build_add_bootstrap_input(options, entry_point)")
expect(cli_src).to_contain("normalized = normalized.push(arg)")
expect(cli_src).to_contain("normalized = normalized.push(\"simple-core\")")
expect(cli_src.contains("bootstrap_input_0 = inputs[0]")).to_equal(false)
expect(cli_src.contains("cli_native_build_with_bootstrap_inputs")).to_equal(false)
expect(cli_src.contains("\n            normalized.push(")).to_equal(false)
expect(cli_src.contains("\n        normalized.push(arg)")).to_equal(false)
expect(driver_src).to_contain("if self.ctx.options.bootstrap_input_count > 0:")
expect(driver_src).to_contain("driver_inputs = driver_inputs + [self.ctx.options.bootstrap_input_0]")
expect(driver_src).to_contain("self.ctx.options.bootstrap_input_count <= 6")
expect(driver_src).to_contain("val input_len = driver_inputs.len()")
expect(driver_src).to_contain("val input_path = driver_inputs[i]")
```

</details>

#### parses the explicit native-build entry from fixed bootstrap inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver_src = file_read("src/compiler/80.driver/driver.spl")
expect(driver_src).to_contain("val requested_entry_match = native_entry != \"\"")
expect(driver_src).to_contain("if native_entry_closure or requested_entry_match or _driver_is_bootstrap_entry_source")
expect(driver_src).to_contain("if not requested_entry_match:")
```

</details>

#### assigns driver source arrays after push for native JIT

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver_src = file_read("src/compiler/80.driver/driver.spl")
val loading_src = file_read("src/compiler/80.driver/driver_source_loading.spl")
expect(driver_src).to_contain("all_sources = all_sources.push(s)")
expect(driver_src).to_contain("entry_sources = entry_sources.push(source)")
expect(loading_src).to_contain("aliases = aliases.push(SourceFile")
expect(loading_src).to_contain("result = result.push(s)")
expect(driver_src.contains("\n                    all_sources.push(s)")).to_equal(false)
expect(driver_src.contains("\n                    entry_sources.push(source)")).to_equal(false)
expect(loading_src.contains("\n        aliases.push(SourceFile")).to_equal(false)
expect(loading_src.contains("\n                result.push(s)")).to_equal(false)
```

</details>

#### assigns native-build entrypoint argv arrays after push for native JIT

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/app/cli/native_build_main.spl")
expect(src).to_contain("args = args.push(raw_args[i])")
expect(src.contains("worker_args = worker_args.push(\"--mode=interpreter\")")).to_equal(false)
expect(src).to_contain("worker_args = worker_args.push(arg)")
expect(src.contains("\n        args.push(raw_args[i])")).to_equal(false)
expect(src.contains("\n        worker_args.push(arg)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native-build JIT ambiguity source guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
