# Native font acceptance exits 132 before its first summary

## Status

Open pure-native compiler/runtime blocker. Focused fixes landed for every
confirmed local fault, but the canonical shaping, 2D-surface, and GPU-emission
specs still exit 132 before a BDD summary. The three-cycle cap is exhausted for
all three specs.

## Confirmed and fixed

- Generated native `fail(...)` now records failure and exits 1 instead of
  falling through a default nil return; the return-valued-helper fixture exits
  1 without SIGILL.
- `font_sffi.load_font` now derives selected identity by path instead of passing
  the boolean result of `selected.?` as a `FontAssetCandidate` payload.
- GPU emission no longer embeds a subprocess self-test in its shared core-C
  process, no longer reads files through raw `rt_file_read_text`, and guards
  plan indices after length assertions. The isolated Vulkan provenance
  self-test passes.
- Engine3D CPU compatibility remains in its focused 3D unit lane, so the 2D
  surface spec no longer closes over optional Vulkan symbols.
- FontRenderer and Vulkan quarantine locks now use explicit free-function mutex
  calls, avoiding the confirmed native method-receiver loss at `Mutex.lock` and
  `Mutex.unlock`; the next surface trap remains under cached-object analysis.
- Font configuration, atlas-owner, and atlas-cache identity now have explicit
  receiver free functions. Existing methods delegate for source compatibility,
  while `font_renderer` uses the free configuration identity path. The focused
  pure-Simple Cranelift spec passes (1 example, 0 failures); canonical font
  acceptance remains capped and is not claimed green by this incremental fix.

## Retained evidence

- `build/test-artifacts/shared_multilingual_gpu_fonts/shared_font_shaping_acceptance_spec_cycle{1,2,3}.log`
- `build/test-artifacts/shared_multilingual_gpu_fonts/gpu_font_emission_spec_cycle{1,2,3}.log`
- `build/test-artifacts/shared_multilingual_gpu_fonts/shared_font_surfaces_spec_cycle{1,2,3}.log`
- `build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/fail_fast_return_helper_v3.log`
- `build/test-artifacts/shared_multilingual_gpu_fonts/vulkan_provenance_self_test.log`
- `build/test-artifacts/shared_multilingual_gpu_fonts/unit/font_identity_free_function_spec_cycle3.log`
- `build/test-artifacts/shared_multilingual_gpu_fonts/option_class_payload_probe_bounded/results.tsv`
- `build/test-artifacts/shared_multilingual_gpu_fonts/option_class_payload_probe_bounded/option-class-profile.log`

## CUDA semantics-v2 handoff update

The CUDA-only portable-compute checker independently rebuilt and authenticated
the semantics-v2 font artifact (PTX SHA-256
`68c258c24e27204c4acade63561cfab3f741a2135b43e5124118eb8b48598bc1`),
including source/version pins and tamper rejection. The smaller
`cuda_generated_font_handoff_spec.spl` then built successfully with the pinned
pure-Simple compiler and core-C runtime, but its native binary exited 132 before
printing a BDD summary. Therefore the CUDA production-pin change remains
uncommitted: static artifact authentication is green, while native acceptance
is still blocked by this existing pure-native execution defect.

## Next fix targets

Cached surface cycle 2 disassembly proved the batch had not returned: native
method-call lowering dropped the `Mutex` receiver. The explicit-argument mutex
repair is present in cycle 3. Execution advances to `warm.atlas_owner_identity()`,
whose generated call again omits its receiver; `_font_render_batch_with_config`
also passes the batch where `config.identity()` requires the config receiver.
Object review further proves immutable instance `fn` calls behave like MIR's
`StaticMethod` arm: an explicit-argument call shifts arguments left, whereas
mutable `me` methods retain their receiver. This is a broader method-resolution
or flag-roundtrip defect, not a mutex, batch-return, or Cranelift argument
forwarding defect. The font identity free-function compatibility path is green;
GPU backend call-site migration and the compiler root guard remain follow-up
work. Shaping cycle 3 proves the path-based identity
repair is active, then
`val owned = handle.?` stores `rt_is_some(handle)` (boolean `1`) instead of the
`FontHandle` payload and traps at the first `owned.handle`. Track pure-native
optional-class payload lowering and deployed-compiler freshness; the current
`ExistsCheck` source already states that the base payload must be preserved.
Inspect emission's final cached `spl_main` object in a fresh session; do not
rerun either capped spec unchanged.

The uncapped native smoke case `option_class_payload` now isolates the shaping
construct (`Box?` followed by `pending.?` and a field read). The retained font
compiler produced no build diagnostics for more than five minutes; the bounded
30-second generic rerun records an XFAIL instead of hanging the matrix. A
separate canonical core-C/entry-closure profile builds the one-module probe in
0.8 seconds, but its binary reports `field access on nil receiver` at
`owned.value` and exits 132. This proves class-Option payload corruption rather
than a font or linker failure. Promote case 20 to a required PASS when a
redeployed pure-Simple compiler returns 7; only then spend a fresh canonical
shaping cycle.

## Clean incremental fix attempt

After the CUDA font readback passed, a detached worktree at `85ace4faa19`
was given only the candidate `ExistsCheck` change: call
`rt_unwrap_or_self` for the present branch and preserve the recorded
`Option::Some` struct identity. This targets the observed boxed-enum handle
being used as the `Box` receiver while leaving flat nullable payloads intact.

The candidate is not admitted. Three bounded compiler-build attempts stopped
at the runtime boundary before the existing class-Option probe could run:

- `core-c-bootstrap` linked the pure-Simple compiler objects but lacked the
  hosted Cranelift/SFFI and directory symbols;
- the legacy `rust-hosted` bundle is explicitly removed; and
- `simple-core` reported that no admitted simple-core runtime archive exists.

Logs and the high-level review outcome are retained under
`build/test-artifacts/shared_multilingual_gpu_fonts/option_class_payload_fix_attempt/`.
The candidate source hunk was removed after review found three semantic
blockers: boxed `None` still uses a mismatched discriminant, the global
`Option::Some` struct-name slot can collide across payload types, and a flat
`Option<Enum>` payload is ambiguous with the boxed enum handle. Do not claim
the class payload fixed or promote native-smoke case 20 until a representation
rule resolves all three, a new pure-Simple compiler builds, and the unchanged
probe exits exactly 7.
