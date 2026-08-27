# Contract spec: test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl` and a green Results line.

## Scenarios

### native-build JIT ambiguity source guards

#### keeps codegen cleanup owner-specific until seed receiver typing is retired

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps codegen cleanup owner-specific until seed receiver typing is retired


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps codegen cleanup owner-specific until seed receiver typing is retired")
val backend_src = file_read("src/compiler/70.backend/backend/compiler.spl")
val codegen_src = file_read("src/compiler/70.backend/codegen.spl")
val driver_src = file_read(
    "src/compiler/80.driver/driver_pipeline_execution.spl")
expect(backend_src).to_contain("compiled.release_codegen_module()")
expect(codegen_src).to_contain("fn release_codegen_module():")
expect(driver_src).to_contain("compiled.release_codegen_module()")
expect(backend_src).to_not_contain("rt_jit_cleanup")        expect(codegen_src).to_not_contain("rt_jit_cleanup")        expect(driver_src).to_not_contain("rt_jit_cleanup")
```

</details>

#### keeps template instantiation progress tracking off Set mutation assignment

- keeps template instantiation progress tracking off Set mutation assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps template instantiation progress tracking off Set mutation assignment")
val src = file_read("src/compiler/40.mono/instantiation.spl")
expect(src).to_contain("in_progress: [text]")
expect(src).to_contain("self.in_progress = self.in_progress.push(key)")
# Cleanup writes through the owner (COW-alias class, 2026-08-21): a
# helper taking and returning the field aliased it and deep-copied it.
expect(src).to_contain("self._drop_in_progress(key)")
expect(src).to_not_contain("_template_remove_text")        expect(src).to_not_contain("in_progress: Set<text>")        expect(src).to_not_contain("self.in_progress = self.in_progress.insert(key)")        expect(src).to_not_contain("self.in_progress = self.in_progress.remove(key)")
```

</details>

#### keeps lazy linker instantiation progress tracking off Set mutation assignment

- keeps lazy linker instantiation progress tracking off Set mutation assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps lazy linker instantiation progress tracking off Set mutation assignment")
val src = file_read("src/compiler/70.backend/linker/lazy_instantiator.spl")
expect(src).to_contain("in_progress: [text]")
expect(src).to_contain("self.in_progress = self.in_progress.push(symbol)")
expect(src).to_contain("lazyinstantiator_drop_in_progress(self, symbol)")
expect(src).to_not_contain("_lazy_remove_text")        expect(src).to_not_contain("in_progress: Set<text>")        expect(src).to_not_contain("self.in_progress = self.in_progress.insert(symbol)")        expect(src).to_not_contain("self.in_progress = self.in_progress.remove(symbol)")
```

</details>

#### keeps compatibility JIT progress tracking off Set mutation assignment

- keeps compatibility JIT progress tracking off Set mutation assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps compatibility JIT progress tracking off Set mutation assignment")
val src = file_read("src/compiler/99.loader/jit_instantiator.spl")
expect(src).to_contain("in_progress: [text]")
expect(src).to_contain("self.in_progress = self.in_progress.push(name)")
expect(src).to_contain("self._drop_in_progress(name)")
expect(src).to_not_contain("_jit_remove_text")        expect(src).to_not_contain("in_progress: Set<text>")        expect(src).to_not_contain("self.in_progress = self.in_progress.insert(name)")        expect(src).to_not_contain("self.in_progress = self.in_progress.remove(name)")
```

</details>

#### keeps linker symbol collection and unresolved tracking receiver-explicit

- keeps linker symbol collection and unresolved tracking receiver-explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps linker symbol collection and unresolved tracking receiver-explicit")
val src = file_read("src/compiler/70.backend/linker/link.spl")
expect(src).to_contain("unresolved: [text]")
expect(src).to_contain("val smf_reader: SmfReaderImpl = reader")
expect(src).to_contain("for symbol in smf_reader.exported_symbols():")
expect(src).to_contain("not self.unresolved.contains(symbol.name)")
expect(src).to_contain("self.unresolved = self.unresolved.push(symbol.name)")
expect(src).to_not_contain("unresolved: Set<text>")        expect(src).to_not_contain("for symbol in reader.exported_symbols():")        expect(src).to_not_contain("\n                        self.unresolved.push(symbol.name)")
```

</details>

#### removes the dead generic backend run_module ambiguity surface

- removes the dead generic backend run_module ambiguity surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes the dead generic backend run_module ambiguity surface")
val src = file_read("src/compiler/80.driver/driver.spl")
expect(src).to_not_contain("fn run_module(backend: Backend, module: HirModule)")        expect(src).to_not_contain("backend.process_module(module)")
```

</details>

#### keeps SFFI process spec generation off the generic process_module name

- keeps SFFI process spec generation off the generic process_module name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps SFFI process spec generation off the generic process_module name")
val workspace_src = file_read("src/compiler/90.tools/sffi_gen/sffi_gen_workspace.spl")
val process_src = file_read("src/compiler/90.tools/sffi_gen/specs/process_mod.spl")
val init_src = file_read("src/compiler/90.tools/sffi_gen/specs/__init__.spl")
expect(workspace_src).to_contain("sffi_process_module()")
expect(process_src).to_contain("fn sffi_process_module() -> ModuleSpec:")
expect(init_src).to_contain("export sffi_process_module")
expect(workspace_src).to_not_contain("process_module()")        expect(process_src).to_not_contain("fn process_module() -> ModuleSpec:")
```

</details>

#### keeps VHDL codegen helpers off ambiguous array push calls

- keeps VHDL codegen helpers off ambiguous array push calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps VHDL codegen helpers off ambiguous array push calls")
val src = file_read("src/compiler/80.driver/driver_compile_vhdl_codegen.spl")
expect(src).to_contain("body_lines = body_lines + [raw_line]")
expect(src).to_contain("ports = ports + [clock_port]")
expect(src).to_contain("sanitized = sanitized + [port_name]")
expect(src).to_not_contain("body_lines = body_lines.push(raw_line)")        expect(src).to_not_contain("ports = ports.push(clock_port)")        expect(src).to_not_contain("ports = ports.push(\"        ")        expect(src).to_not_contain("sanitized = sanitized.push(port_name)")
```

</details>

#### keeps EffectEnv dirty tracking off Set insert and clear

- keeps EffectEnv dirty tracking off Set insert and clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps EffectEnv dirty tracking off Set insert and clear")
val src = file_read("src/compiler/00.common/effects.spl")
expect(src).to_contain("dirty: [Symbol]")
expect(src).to_contain("_effect_symbol_append_unique(self.dirty, sym)")
expect(src).to_contain("self.dirty = []")
expect(src).to_not_contain("dirty: Set<Symbol>")        expect(src).to_not_contain("self.dirty.insert(sym)")        expect(src).to_not_contain("self.dirty.clear()")
```

</details>

#### passes native-build driver inputs through fixed bootstrap slots

- passes native-build driver inputs through fixed bootstrap slots


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes native-build driver inputs through fixed bootstrap slots")
# Repointed 2026-08-21: driver.spl was split in 4b88aebf00b; the fixed
# bootstrap-input block moved verbatim to driver_source_pipeline_loading.spl.
val cli_src = file_read("src/app/io/_CliCompile/compile_targets.spl")
val driver_src = file_read("src/compiler/80.driver/driver_source_pipeline_loading.spl")
expect(cli_src).to_contain("fn cli_native_build_add_bootstrap_input")
expect(cli_src).to_contain("options = cli_native_build_add_bootstrap_input(options, cf)")
expect(cli_src).to_contain("options = cli_native_build_add_bootstrap_input(options, source_dir)")
expect(cli_src).to_contain("options = cli_native_build_add_bootstrap_input(options, entry_point)")
expect(cli_src).to_contain("normalized = normalized.push(arg)")
expect(cli_src).to_contain("normalized = normalized.push(\"simple-core\")")
expect(cli_src).to_not_contain("bootstrap_input_0 = inputs[0]")        expect(cli_src).to_not_contain("cli_native_build_with_bootstrap_inputs")        expect(cli_src).to_not_contain("\n            normalized.push(")        expect(cli_src).to_not_contain("\n        normalized.push(arg)")        expect(driver_src).to_contain("if self.ctx.options.bootstrap_input_count > 0:")
expect(driver_src).to_contain("driver_inputs = driver_inputs + [self.ctx.options.bootstrap_input_0]")
expect(driver_src).to_contain("self.ctx.options.bootstrap_input_count <= 6")
expect(driver_src).to_contain("val input_len = driver_inputs.len()")
expect(driver_src).to_contain("val input_path = driver_inputs[i]")
```

</details>

#### parses the explicit native-build entry from fixed bootstrap inputs

- parses the explicit native-build entry from fixed bootstrap inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the explicit native-build entry from fixed bootstrap inputs")
# Repointed 2026-08-21: entry parsing moved to driver_source_pipeline_parsing.spl
# in the driver.spl split (4b88aebf00b).
val driver_src = file_read("src/compiler/80.driver/driver_source_pipeline_parsing.spl")
expect(driver_src).to_contain("val requested_entry_match = native_entry != \"\"")
expect(driver_src).to_contain("if native_entry_closure or requested_entry_match or _driver_is_bootstrap_entry_source")
expect(driver_src).to_contain("if not requested_entry_match:")
```

</details>

#### assigns driver source arrays after push for native JIT

- assigns driver source arrays after push for native JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns driver source arrays after push for native JIT")
# Repointed 2026-08-21: the driver.spl split (4b88aebf00b) put the
# all_sources loop in driver_source_pipeline_loading.spl and the
# entry_sources loop in driver_source_pipeline_parsing.spl.
val pipeline_loading_src = file_read("src/compiler/80.driver/driver_source_pipeline_loading.spl")
val driver_src = file_read("src/compiler/80.driver/driver_source_pipeline_parsing.spl")
val loading_src = file_read("src/compiler/80.driver/driver_source_loading.spl")
expect(pipeline_loading_src).to_contain("all_sources = all_sources.push(s)")
expect(driver_src).to_contain("entry_sources = entry_sources.push(source)")
expect(loading_src).to_contain("aliases = aliases.push(SourceFile")
expect(loading_src).to_contain("result = result.push(s)")
expect(pipeline_loading_src).to_not_contain("\n                    all_sources.push(s)")        expect(driver_src).to_not_contain("\n                    entry_sources.push(source)")        expect(loading_src).to_not_contain("\n        aliases.push(SourceFile")        expect(loading_src).to_not_contain("\n                result.push(s)")
```

</details>

#### assigns native-build entrypoint argv arrays after push for native JIT

- assigns native-build entrypoint argv arrays after push for native JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns native-build entrypoint argv arrays after push for native JIT")
val src = file_read("src/app/cli/native_build_main.spl")
expect(src).to_contain("args = args.push(raw_args[i])")
expect(src).to_not_contain("worker_args = worker_args.push(\"--mode=interpreter\")")        expect(src).to_contain("worker_args = worker_args.push(arg)")
expect(src).to_not_contain("\n        args.push(raw_args[i])")        expect(src).to_not_contain("\n        worker_args.push(arg)")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c291c5eb9278bb48e60d9be72b9fd9b2153be2157cbd07ffe1942cc06098137f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c291c5eb9278bb48e60d9be72b9fd9b2153be2157cbd07ffe1942cc06098137f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c291c5eb9278bb48e60d9be72b9fd9b2153be2157cbd07ffe1942cc06098137f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps codegen cleanup owner-specific until seed receiver typing is retired' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps template instantiation progress tracking off Set mutation assignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps lazy linker instantiation progress tracking off Set mutation assignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
