# Cached interpolation lost during monomorphization

Status: causal native-producer diagnosis; source repair and regressions prepared.
Corrected-producer qualification remains pending root's final cycle 3. Bug DB
reconciliation is pending a qualified database tool. PR #2881 is not causal.

## Frozen failure

Source: `c2a88e77ec2847e63cdc540e726ed38f11e6a88b` in
`/home/yoon/dev/simple-owned-fixes-qualification-20261011`.
Producer SHA256: `e05e69a2539bb417eda6519d98666ed244f93fdb7db38e92224f58e80f8af178`.
Capsule: `/tmp/release-owned-cycle2-runtime-capsules/<producer-sha>/simple`.

The unchanged `test/fixtures/bootstrap/stage2_micro/diff_generic_struct_field/main.spl`
compiled successfully for ARM (ELF machine 183), ran with exit 0, but printed
`joined={joined}` instead of required `joined=ab`. Artifact SHA256:
`9deea51f3a5fd1283991a3e88dfea0ea0c3e3134e486c195c4b4182a944d7c9e`.
The queue's `build/native_probe/release-owned-cycle2-20261011/fixture-evidence.json`
and `fixtures/typeparam_control/arm/{build.log,run.stdout}` retain the failure.
Exit 0 is not a semantic PASS. The final worker consumed one HIR cache hit.

## Exact causal boundary

The cached blob contains `StringLit("joined={joined}", ...)` with present
interpolations, count 1, and a `NamedVar` expression named `joined`.
Read-only GDB diagnostics called real functions in the frozen producer:

1. `hir_module_decode(blob)` followed by the existing Option unwrap and
   `hir_module_encode(module)` preserved that complete interpolation record.
   Whole-module byte equality was false; no canonical byte-stability claim is
   made here. The original and reencoded blobs both have 7,080 bytes.
2. Passing the decoded module through `run_monomorphization_with_report` then
   encoding it changed the same string's interpolation array to present-empty
   (count 0). The resulting module has 6,596 bytes.

No debugger instruction, return value, object field, or source was patched.
These diagnostic calls used CPUs 16–17 with a 40-second timeout. Earlier
diagnostic setup attempts used the wrong frame start / omitted the required
Option unwrap; their failures are retained and are not product evidence.

The causal scripts/logs and all three blobs are under
`/home/yoon/dev/simple-text-search-native-abi-20261011/build/native_probe/interpolation-cycle2/`:
`roundtrip-unwrapped.gdb`, `roundtrip-unwrapped.log`, `after-mono.gdb`,
`after-mono.log`, `blob.txt`, `reencoded.txt`, `after-mono.txt`, `hashes.json`.
SHA256 of `after-mono.log`:
`87979691981bde57769c4bda3c9d1013f755091853679a0193f18d9def8a3388`.

## Owner repair

The generated `hc_dec_hir_expr_kind` constructs `Some(ov6)` for an optional
interpolation array. `MonomorphizationPass.rewrite_expr` instead assumed fresh
flat HIR: `if interps.?: for item in interps`. Presence succeeds on the wrapper,
but iterating that wrapper yields no interpolation elements. The rewrite then
replaces the original list with an empty array. MIR correctly prints the now
plain literal; neither brace-search ABI nor frontend parsing caused this loss.

Unwrap before traversal at all four matching consumers: mono collection and
rewrite, ordinary type substitution, and exhaustive HIR body substitution.
Nil remains nil. A present empty array remains present. Each existing
`var ni = it` copy retains formatting and span while replacing only its
expression. Rebuilt arrays retain the existing return/constructor convention.
There is no codec version change, parser workaround, or fixture/oracle change.

## Regression and final qualification

`test/01_unit/compiler/mono/cached_interpolation_rewrite_spec.spl` compares real
generated-codec output across rewrite and both substitution owners, covering
fresh flat, explicit Some, decoded Some, absent, and present-empty lists.
Full expression equality includes interpolation value, format, and span.

`test/fixtures/compiler/cached_interpolation_generic/main.spl` instantiates a
generic interpolated function at i64 and text, asserting the actual returned
strings before printing its success marker. This exercises generic body
substitution in addition to the unchanged BUG-IT-6 native oracle.

Both corrected native oracles and the new SSpec remain unrun pending root's
corrected Pure-Simple producer. No new compiler construction, seed test runner,
or ARM/RISC-V success claim was made in this repair lane.
