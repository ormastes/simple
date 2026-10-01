# Environment-Optimized Dynamic Libraries

## Current availability

This feature is under implementation. The current product does **not** provide
a supported environment-provider catalog command, automatic parser SIMD tier,
or verified GPU-resident parser execution. Existing SIMD probes, composition
generations, native GPU loading, and structural parsing are foundations, not an
end-to-end capability claim.

## Selected behavior

The product will keep one baseline-safe core and select eligible sibling
provider artifacts at a coarse session/batch boundary. Host execution facts,
generated-code target features, artifact placement, and workload placement are
independent. Eligibility validates exact usable features, ABI, artifact and
dependency identity, semantics, and resource limits before preference ranking.

`prefer` may visibly fall back, `require` fails when unavailable, and `max`
excludes otherwise eligible variants above the compatible architecture preset.
None overrides hardware, OS state, trust, or administrator restrictions.

The initial pilot varies parser providers only after legacy/canonical parity.
Native, SMF, JIT, AOT, and GPU placements share logical contracts but retain
their distinct loaders, binary ABIs, and execution evidence.

The implemented pure resolver models parser `prefer`/`require`, host CPU `max`,
frontend offload, and fallback across CLI, environment, project, user, and
administrator layers. New product CLI/config keys are not wired yet.
Administrator values are restrictions, and effective provenance reports
`admin` when a cap changes the decision. Host execution policy does not consume
generated target-codegen features.

## Evidence interpretation

Do not treat a filename suffix, target flag, loaded symbol, SMF registry entry,
or queued GPU operation as optimized execution. Qualified evidence separately
records requested features, admission, binding, emitted instructions or device
program, actual execution, completion, and resource retirement.

See the finalized requirements and staged plan before implementation or review:

- `doc/02_requirements/feature/environment_optimized_dynamic_libraries.md`
- `doc/02_requirements/nfr/environment_optimized_dynamic_libraries.md`
- `doc/03_plan/compiler/environment_optimized_dynamic_libraries.md`
