# Skip known-ineligible MIR shards before worker setup

## Observed problem

The live Phase3 coordinator on frozen source
`5a164ad0b16c8bcb58406d8960f38910c49c3f0b` scheduled an ordinary MIR shard for
native-build's default `dynload` output. The worker later reported
`lane_ok=false`, `lane_reason='output format re-reads MIR set'`, zero claimed
modules, and zero failed modules, then the coordinator took its normal fallback.
The parent reported roughly fifteen minutes of preceding frontend/cache work;
that elapsed time is an observation from the existing run, not a benchmark of
this repair or evidence that the worker performed MIR lowering.

The active worker (`app.io._CliCompile.compile_targets`) selects `Both` for
ordinary dynload output and for `--emit-smf`. Such output requires the full MIR
set after native codegen, so the driver's refusal is correct. The coordinator
previously omitted that already-known output restriction when scheduling MIR
workers. The bounded operator workaround remains `SIMPLE_MIR_SHARDING=0`.

## Repair and boundaries

`app.cli.native_build_output_plan` now owns the output-format decision shared by
the worker and the coordinator's lightweight argv projection. The worker still
owns complete argument validation. The existing coordinator operand predicate
was moved unchanged; its callers now import it. The standalone-flag predicate
is shared with the worker's validation loop, so output-shaped operands are not
mistaken for output flags.

For nonselective requests with a known `Both` output, the coordinator emits the
existing refusal reason and returns zero parallel workers before worker-budget
calculation, ledger creation, or process spawning. The ordinary final-worker
path remains intact. Explicit native object, entry-object, archive, and shared
outputs retain their prior routing; so does `one-binary` unless `--emit-smf` is
requested. Grouped-native output retains its existing format override.

Unknown options, invalid mode values, and missing operands preserve the prior
worker path. This projection is a scheduling optimization, not new validation
or proof that other lane conditions are eligible. Selective dispatch occurs
before the new preflight and retains its own admission/failure rules. The
worker's authoritative `native_mir_shard_eligible_v1` fail-closed check remains
unchanged. Focused capsules have their own output contract and were not routed
through the ordinary CLI default projection. No artifact/cache identity or
fallback/error policy changed.

## Scoped verification

Isolated source base: `afde58909572613046d692099d03227508a2166d` from
`release/1.0.0`, workspace
`/Users/ormastes/wt/mir-shard-format-preflight-20261025`.
Retained evidence: `build/verify/mir-shard-format-preflight-20261025/`.

| Diagnostic spec | Passed | Failed |
| --- | ---: | ---: |
| `native_build_mir_output_preflight_spec.spl` | 9 | 0 |
| `native_build_shard_admission_spec.spl` | 11 | 0 |
| `native_build_arg_source_spec.spl` | 5 | 0 |
| `native_mir_shard_spec.spl` | 10 | 0 |

The new cases exercise the production shared selector, mode aliases and
last-value behavior, explicit artifacts, SMF side output, operand skipping,
selective bypass, uncertain argv, grouped output, and the coordinator/worker
call-site ordering. Adjacent specs cover existing memory admission, CLI source
contracts, and MIR ledger/outcome behavior. First implementation cycle passed;
no passing suite was repeated. Working/staged direct-env guards and the
spec-document placement check are separate repository gates.

Commands are retained alongside each log as `.log.command`, using
`SIMPLE_LIB=<workspace>/src` and the explicitly authorized existing seed:

```sh
"$EXISTING_SEED" test "$SPEC" --mode=interpreter --no-session-daemon \
  --sequential --no-db --no-cache --assert-ran
```

Producer SHA-256:
`ddd5aa4b9c47433ac814983d7499002a115e9f0e28f4623bfe26dba7e6b0a714`.
This verifies policy and source wiring under the retained diagnostic
interpreter. It does not qualify a rebuilt native coordinator or measure a
fresh bootstrap speedup. No MIR worker, compiler, Phase2, runtime, Cargo, or
full-bootstrap build was launched. The ongoing Phase3 coordinator and both
frozen source worktrees were left unchanged.
