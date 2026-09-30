# Positional bootstrap native-build silently ignored --emit-object

Status: source fix prepared; regression execution and refreshed CLI integration pending.

## Reproduction and evidence

The pure-Simple bootstrap producer `60b93e443922` was invoked on the isolated
`build/native_probe/module_object_probe/module.spl` module with `--emit-object`
and an explicit output/cache directory. Attempt 1 exited 1 after roughly 24
seconds. It tried to link an executable and failed with
`lld-link: error: undefined symbol: __simple_main`.

Evidence: `build/native_probe/module_object_probe/result.json`,
`build.stdout.log`, and `module.obj.link.log`. The link command includes
`/ENTRY:mainCRTStartup` despite the requested object output.

The follow-up using the driver's existing `SIMPLE_NATIVE_BUILD_EMIT_OBJECT=1`
setting succeeded and produced a genuine 566-byte COFF object. Evidence:
`build/native_probe/module_object_probe/result2.json` and `object.readobj.log`.
This establishes the driver path's capability; it does not verify the patched
CLI, which is not in that producer binary.

## Cause and correction

`src/app/cli/bootstrap_main.spl` routed a single positional `.spl` file directly
to the driver without projecting emit flags into its output-mode setting.
The general CLI coordinator already projects these flags, but this path bypasses
it. The missing projection therefore requested an executable requiring an entry
symbol for a module that intentionally has none.

The positional route now projects object/archive/shared flags, rejects conflicting
modes before dispatch, and binds the selected mode around driver construction and
compilation. Its app IO owner preserves absent, empty, and nonempty inherited
values on restoration. Omitted flags retain the prior inherited behavior.
The existing operand classifier is shared with the output-mode parser so option
values that resemble flags cannot select a mode.

The Stage4 strict profile still rejects non-executable modes. The existing
greater-than-300-byte artifact guard remains: this probe's valid 566-byte object
does not demonstrate a need to weaken it. Smaller objects may require a future
format-aware admission policy with direct evidence.

## Validation limits

- Static whitespace validation: PASS (`git diff --check`).
- Eight production parser/environment behavior scenarios:
  `test/01_unit/app/cli/bootstrap_native_output_mode_spec.spl`, UNEXECUTED.
- SSpec documentation generation: UNEXECUTED; no admitted full CLI runner exists
  in this lane. No generated manual or zero-stub result is claimed.
- Refreshed compiler CLI object/archive/shared integration: UNEXECUTED.
- No Rust seed, full rebuild, or previously blocked compiler graph was invoked.

The remaining integration gate must exercise CLI `--emit-object` on the module
without a main function and inspect the emitted object. The environment-only
probe must not be used as evidence that the new CLI projection has passed.
