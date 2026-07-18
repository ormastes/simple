# Stage4 Smoke Gate Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## Scenarios

### bootstrap stage4 smoke gate

#### fails bootstrap when the freshly built full CLI cannot execute code

```simple
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""

expect(script).to_contain("stage4_smoke")
expect(script).to_contain("run_timeout 30")
expect(script).to_contain("-c 'print(1+1)'")
expect(script).to_contain("error: stage4 binary failed smoke test")
```

#### rejects seed fallback and gates the full candidate before deployment

```simple
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val admission = rt_file_read_text("scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs") ?? ""

expect(script).to_contain("refusing seed fallback")
expect(script).to_contain("CANDIDATE_FRONTEND_ROOT=${repo_root}")
expect(script).to_contain(". \"${repo_root}/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs\"")
expect(script).to_contain("if ! simple_binary_is_valid \"${full_bin}\"; then")
expect(admission).to_contain("candidate_frontend_smoke() (")
expect(admission).to_contain("fixtures/p2_add.spl")
expect(admission).to_contain("--runtime-bundle core-c-bootstrap")
expect(admission).to_contain("--mode one-binary")
expect(admission).to_contain("--mode definitely-invalid-mode")
expect(admission).to_contain("trap 'rm -rf \"$probe_dir\"' 0")
expect(admission).to_contain("simple_binary_is_valid() (")
expect(admission).to_contain("version=$(SIMPLE_BINARY=\"$candidate\"")
expect(admission).to_not_contain(" check \\")
expect(script).to_contain("stage4-redeploy-gate")
expect(script).to_contain("redeploy_gate/redeploy_gate.shs")
```

#### builds and requires the dedicated compiler backfill for a full CLI

```simple
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val full_cli_implication: i64 = script.find("if [ \"${deploy}\" -eq 1 ] || [ \"${bootstrap_mode}\" = \"one-binary\" ]; then") ?? -1
val reuse_gate: i64 = script.find("if [ \"${full_bootstrap}\" -eq 0 ]; then") ?? -1

expect(script).to_contain("compiler_backfill_lib=\"src/compiler_rust/target/bootstrap/${archive_prefix}simple_compiler_backfill${archive_suffix}\"")
expect(script).to_contain("-p simple-compiler-backfill")
expect(script).to_contain("full CLI bootstrap needs the compiler backfill archive")
expect(script).to_contain("full CLI bootstrap refuses a stale compiler backfill")
expect(script).to_contain("rust_rebuilt=1")
expect(script).to_contain("[ \"${rust_rebuilt}\" -eq 1 ]")
expect(script).to_contain("Stage 4 full-CLI capsule preparation is currently Linux-only")
expect(full_cli_implication).to_be_less_than(reuse_gate)
```

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl` |
| Updated | 2026-07-15 |
| Generator | `simple spipe-docgen` compatible manual |

The wrapper self-test is the executable behavioral oracle for the shared shell
admission helper. These source-contract scenarios additionally prove that the
bootstrap pipeline sources that helper and gates the Stage4 candidate before
deployment; they do not claim a current-source Stage4 build.
