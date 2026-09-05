# frontend_offload_switch_spec

> The compiler frontend leaves the CPU only when one typed switch says so.

<!-- sdn-diagram:id=frontend_offload_switch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=frontend_offload_switch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

frontend_offload_switch_spec -> std
frontend_offload_switch_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=frontend_offload_switch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# frontend_offload_switch_spec

The compiler frontend leaves the CPU only when one typed switch says so.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `/home/yoon/dev/simple-gpu-frontend/test/01_unit/compiler/structural/frontend_offload_switch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

The compiler frontend leaves the CPU only when one typed switch says so.
    The switch is resolved from CLI, env, and project config, in that order.

## Scenarios

### Frontend offload switch resolution

#### lets the CLI value beat env and config

- Resolve the frontend offload switch from CLI, env, and config
   - Expected: sw.mode equals `OffloadMode.ResidentGpu`
   - Expected: sw.source equals `cli`
   - Expected: sw.raw equals `resident`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-1
step("Resolve the frontend offload switch from CLI, env, and config")
val sw = resolved("resident", "on", "off")
expect(sw.mode).to_equal(OffloadMode.ResidentGpu)
expect(sw.source).to_equal("cli")
expect(sw.raw).to_equal("resident")
```

</details>

#### lets the env value beat config when the CLI is absent

- Resolve the frontend offload switch from CLI, env, and config
   - Expected: sw.mode equals `OffloadMode.HybridVectorGpu`
   - Expected: sw.source equals `env`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-1
step("Resolve the frontend offload switch from CLI, env, and config")
val sw = resolved("", "on", "off")
expect(sw.mode).to_equal(OffloadMode.HybridVectorGpu)
expect(sw.source).to_equal("env")
```

</details>

#### uses the config value when CLI and env are absent

- Resolve the frontend offload switch from CLI, env, and config
   - Expected: sw.mode equals `OffloadMode.ResidentGpu`
   - Expected: sw.source equals `config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-1
step("Resolve the frontend offload switch from CLI, env, and config")
val sw = resolved("", "", "resident")
expect(sw.mode).to_equal(OffloadMode.ResidentGpu)
expect(sw.source).to_equal("config")
```

</details>

#### defaults to CPU reference from source default when nothing is set

- Default to CPU reference when nothing is set
   - Expected: sw.mode equals `OffloadMode.CpuReference`
   - Expected: sw.auto is false
   - Expected: sw.fallback equals `OffloadFallbackPolicy.AllowCpu`
   - Expected: sw.source equals `default`
   - Expected: sw.raw equals `off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-1
step("Default to CPU reference when nothing is set")
val sw = resolved("", "", "")
expect(sw.mode).to_equal(OffloadMode.CpuReference)
expect(sw.auto).to_equal(false)
expect(sw.fallback).to_equal(OffloadFallbackPolicy.AllowCpu)
expect(sw.source).to_equal("default")
expect(sw.raw).to_equal("off")
```

</details>

#### accepts off, on, resident, and auto

- Resolve the frontend offload switch from CLI, env, and config
   - Expected: parse_frontend_offload_value("off").unwrap().mode equals `OffloadMode.CpuReference`
   - Expected: parse_frontend_offload_value("on").unwrap().mode equals `OffloadMode.HybridVectorGpu`
   - Expected: parse_frontend_offload_value("resident").unwrap().mode equals `OffloadMode.ResidentGpu`
   - Expected: auto.mode equals `OffloadMode.CpuReference`
   - Expected: auto.auto is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-1
step("Resolve the frontend offload switch from CLI, env, and config")
expect(parse_frontend_offload_value("off").unwrap().mode).to_equal(OffloadMode.CpuReference)
expect(parse_frontend_offload_value("on").unwrap().mode).to_equal(OffloadMode.HybridVectorGpu)
expect(parse_frontend_offload_value("resident").unwrap().mode).to_equal(OffloadMode.ResidentGpu)
val auto = parse_frontend_offload_value("auto").unwrap()
expect(auto.mode).to_equal(OffloadMode.CpuReference)
expect(auto.auto).to_equal(true)
```

</details>

#### treats hybrid as an alias of on

- Resolve the frontend offload switch from CLI, env, and config
   - Expected: sw.mode equals `OffloadMode.HybridVectorGpu`
   - Expected: sw.raw equals `hybrid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-1
step("Resolve the frontend offload switch from CLI, env, and config")
val sw = resolved("hybrid", "", "")
expect(sw.mode).to_equal(OffloadMode.HybridVectorGpu)
expect(sw.raw).to_equal("hybrid")
```

</details>

#### rejects an unknown value naming the value and its source

- Resolve the frontend offload switch from CLI, env, and config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-1
step("Resolve the frontend offload switch from CLI, env, and config")
val e = err_text(resolve_frontend_offload(inputs("", "bogus", "")))
expect(e).to_contain("bogus")
expect(e).to_contain("env")
```

</details>

#### resolves the fallback policy from require-requested

- Refuse to demote under require-requested
   - Expected: sw.fallback equals `OffloadFallbackPolicy.RequireRequested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-3
step("Refuse to demote under require-requested")
val sw = resolve_frontend_offload(inputs_with_fallback("on", "require-requested")).unwrap()
expect(sw.fallback).to_equal(OffloadFallbackPolicy.RequireRequested)
val e = err_text(resolve_frontend_offload(inputs_with_fallback("on", "sometimes")))
expect(e).to_contain("sometimes")
```

</details>

### Frontend offload profile

#### changes only the LexStructure and Parse stage modes and still validates

- Resolve the frontend offload switch from CLI, env, and config
   - Expected: profile.stage_modes.len() equals `8`
   - Expected: profile.stage_modes[1] equals `OffloadMode.ResidentGpu`
   - Expected: profile.stage_modes[2] equals `OffloadMode.ResidentGpu`
   - Expected: profile.stage_modes[i] equals `OffloadMode.CpuReference`
   - Expected: validate_offload_profile(profile) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-4
step("Resolve the frontend offload switch from CLI, env, and config")
val profile = frontend_offload_profile(resolved("resident", "", ""))
expect(profile.stage_modes.len()).to_equal(8)
expect(profile.stage_modes[1]).to_equal(OffloadMode.ResidentGpu)
expect(profile.stage_modes[2]).to_equal(OffloadMode.ResidentGpu)
for i in [0, 3, 4, 5, 6, 7]:
    expect(profile.stage_modes[i]).to_equal(OffloadMode.CpuReference)
expect(validate_offload_profile(profile)).to_equal(Ok(()))
```

</details>

### Frontend offload decision

#### keeps CPU reference with no reason when the switch is off

- Default to CPU reference when nothing is set
   - Expected: d.requested equals `OffloadMode.CpuReference`
   - Expected: d.selected equals `OffloadMode.CpuReference`
   - Expected: d.fallback_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-2
step("Default to CPU reference when nothing is set")
val d = frontend_offload_decision(resolved("", "", ""), false).unwrap()
expect(d.requested).to_equal(OffloadMode.CpuReference)
expect(d.selected).to_equal(OffloadMode.CpuReference)
expect(d.fallback_reason).to_equal("")
```

</details>

#### demotes auto with the auto-profile reason instead of looking like off

- Demote honestly when GPU parsing is unimplemented
   - Expected: d.selected equals `OffloadMode.CpuReference`
   - Expected: d.fallback_reason equals `auto_profile_not_implemented_wave_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-3
step("Demote honestly when GPU parsing is unimplemented")
val d = frontend_offload_decision(resolved("auto", "", ""), false).unwrap()
expect(d.selected).to_equal(OffloadMode.CpuReference)
expect(d.fallback_reason).to_equal("auto_profile_not_implemented_wave_1")
expect(frontend_offload_receipt_line(d, "cli")).to_equal(
    "[frontend-offload] requested=cpu_reference selected=cpu_reference reason=auto_profile_not_implemented_wave_1 source=cli")
```

</details>

#### refuses auto under require-requested because no crossover evidence is retained

- Refuse to demote under require-requested
   - Expected: d.is_err() is true
   - Expected: d.unwrap_err() equals `frontend_offload_required_mode_unavailable: auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-3
step("Refuse to demote under require-requested")
val switch = resolve_frontend_offload(inputs_with_fallback("auto", "require-requested")).unwrap()
val d = frontend_offload_decision(switch, false)
expect(d.is_err()).to_equal(true)
expect(d.unwrap_err()).to_equal("frontend_offload_required_mode_unavailable: auto")
```

</details>

#### demotes on to CPU reference with parse_mode_unimplemented under allow-cpu

- Demote honestly when GPU parsing is unimplemented
   - Expected: d.requested equals `OffloadMode.HybridVectorGpu`
   - Expected: d.selected equals `OffloadMode.CpuReference`
   - Expected: d.fallback_reason equals `parse_mode_unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-3
step("Demote honestly when GPU parsing is unimplemented")
val d = frontend_offload_decision(resolved("on", "", ""), false).unwrap()
expect(d.requested).to_equal(OffloadMode.HybridVectorGpu)
expect(d.selected).to_equal(OffloadMode.CpuReference)
expect(d.fallback_reason).to_equal("parse_mode_unimplemented")
```

</details>

#### demotes resident to CPU reference with parse_mode_unimplemented under allow-cpu

- Demote honestly when GPU parsing is unimplemented
   - Expected: d.requested equals `OffloadMode.ResidentGpu`
   - Expected: d.selected equals `OffloadMode.CpuReference`
   - Expected: d.fallback_reason equals `parse_mode_unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-3
step("Demote honestly when GPU parsing is unimplemented")
val d = frontend_offload_decision(resolved("resident", "", ""), false).unwrap()
expect(d.requested).to_equal(OffloadMode.ResidentGpu)
expect(d.selected).to_equal(OffloadMode.CpuReference)
expect(d.fallback_reason).to_equal("parse_mode_unimplemented")
```

</details>

#### refuses to demote on under require-requested

- Refuse to demote under require-requested


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-3
step("Refuse to demote under require-requested")
val sw = resolve_frontend_offload(inputs_with_fallback("on", "require-requested")).unwrap()
val r = frontend_offload_decision(sw, false)
match r:
    case Ok(_): expect("Ok").to_equal("Err")
    case Err(e): expect(e).to_equal("frontend_offload_required_mode_unavailable: hybrid_vector_gpu")
```

</details>

#### selects the requested mode when GPU parsing is available

- Demote honestly when GPU parsing is unimplemented
   - Expected: d.selected equals `OffloadMode.HybridVectorGpu`
   - Expected: d.fallback_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-3
step("Demote honestly when GPU parsing is unimplemented")
val d = frontend_offload_decision(resolved("on", "", ""), true).unwrap()
expect(d.selected).to_equal(OffloadMode.HybridVectorGpu)
expect(d.fallback_reason).to_equal("")
```

</details>

#### maps the selected mode to the parse mode text

- Record the offload decision receipt
   - Expected: frontend_offload_parse_mode_text(off) equals `cpu_reference`
   - Expected: frontend_offload_parse_mode_text(on) equals `hybrid_vector_gpu`
   - Expected: frontend_offload_parse_mode_text(resident) equals `resident_gpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-2
step("Record the offload decision receipt")
val off = frontend_offload_decision(resolved("", "", ""), false).unwrap()
expect(frontend_offload_parse_mode_text(off)).to_equal("cpu_reference")
val on = frontend_offload_decision(resolved("on", "", ""), true).unwrap()
expect(frontend_offload_parse_mode_text(on)).to_equal("hybrid_vector_gpu")
val resident = frontend_offload_decision(resolved("resident", "", ""), true).unwrap()
expect(frontend_offload_parse_mode_text(resident)).to_equal("resident_gpu")
```

</details>

#### records the receipt line with requested, selected, reason, and source

- Record the offload decision receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req AC-3
step("Record the offload decision receipt")
val sw = resolved("", "on", "")
val d = frontend_offload_decision(sw, false).unwrap()
expect(frontend_offload_receipt_line(d, sw.source)).to_equal(
    "[frontend-offload] requested=hybrid_vector_gpu selected=cpu_reference reason=parse_mode_unimplemented source=env")
val off = frontend_offload_decision(resolved("", "", ""), false).unwrap()
expect(frontend_offload_receipt_line(off, "default")).to_equal(
    "[frontend-offload] requested=cpu_reference selected=cpu_reference reason= source=default")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `39f62d1df64b613668f73681feb092f6915ebb9972bd1dcea780a219538a43c5`
