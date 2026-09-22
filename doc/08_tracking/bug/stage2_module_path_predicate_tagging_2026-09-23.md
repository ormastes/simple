# Stage2 module-name normalization loses prefix/suffix matches

Status: canonical path containment native red/green PASS; independent Astra
review PASS approves the focused commit. Generic MIR predicate-argument
representation defect OPEN.
The separate intermittent capsule identity rejection remains OPEN.
Base: `1ea851cf6c912804ac24f5eefbaf70924531ac4c`.

## Root cause and bounded correction

The preserved positional Stage3-route admission produced
`src.app.cli.bootstrap_main.spl`, `src.compiler.driver.driver.spl`, and
`app.cli.main.spl` instead of their canonical root/suffix-stripped names.
The now-fixed Cranelift qualified-definition policy is not the cause and is
unchanged by this patch.

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` normalizes the
starts_with/ends_with receiver, but still manually runs the argument through
raw rt_strlen then rt_string_new. Cranelift's Str lowering produces a tagged
rt_string_new_literal result. rt_strlen delegates to raw spl_str_len/strlen,
so this argument path reads a tagged string object's bytes rather than its
text. Frozen ARM64 disassembly confirms that sequence: src/ literal at0x18c8,
rt_strlen at0x18e0, rt_string_new at0x1900, starts_with at0x1920; suffix path
at0x1a14/0x1a2c/0x1a4c/0x1a6c. Unlike receiver normalization, no rt_interp_cstr
intervenes. This explains the false predicates; native red confirms the
result. The generic lowering defect is recorded here, not claimed fixed.

The canonical module_path_naming function now uses one private checked byte
matcher for its five fixed prefix/suffix decisions. It rejects negative start,
start beyond length, and insufficient remaining bytes in separate guards
before indexing. Markers are at most4 bytes. No string retagging, substring
copy, allocation, or new full-path scan is introduced by these comparisons.

Policy is unchanged: normalize backslashes; strip repeated leading ../ and
then one ./; take the first /src/ before considering /examples/; strip a
leading src/; remove one terminal lowercase .spl or .sdn; retain existing
numbered-component and punctuation handling. No broad grammar workaround is
silently normalized: the generic MIR repair needs its own verified lane.

## Production-path evidence

Worktree: `/Users/ormastes/simple-tmp/stage2-module-path-normalization-20260923`.
Evidence: `build/native_probe/module-path-normalization`.
Frozen producer: private executable copy of the rejected Stage2 candidate
from `stage2-symbol-names-1ea851c/frozen-failure/simple-stage2`, SHA256
`02c36988e4f47fbfda74248ead4a7633011179fa00728eb75642e071c83dbe35`.
This explicitly authorized bootstrap diagnostic does not admit that rejected
candidate as a general runner. No seed SPipe or general test execution occurs.

`test/fixtures/native/module_path_normalization.spl` imports the actual
production function, with no extracted/model implementation. Its26 exact
cases cover the original failures, Windows separators, non-ASCII workspace,
relative paths, source/example precedence, competing source roots, numbered
directory boundaries, punctuation, short/empty inputs, and negative root/
suffix lookalikes. Every mismatch prints its exact expected/actual pair and
contributes to nonzero exit; a pass requires all26 and the pass marker.

Three compiler cycles, all caches private:

1. Baseline positional native compile succeeds. Executable exits24 and prints
   all24 mismatches. Only unchanged empty/src inputs pass. red-build12.18s,
   maximum process RSS538738688 bytes; red-run0.36s, RSS10633216 bytes.
2. Patched positional compile emits both objects, but rejects the module
   capsule with identity-invalid before link. This is NOT a compiler PASS.
   The exact emitted objects are copied to green-module.o/green-fixture.o.
   green-build1.77s, process RSS248922112 bytes.
3. Final diagnostic LLDB compile retains the gate and places a conditional
   breakpoint at identity_valid+0x150 for false0/3. No false predicate hits;
   native compile/link finishes and the inferior exits0. The subsequent
   debugger bt command errors because the process already exited, so LLDB
   itself exits1. No predicate state could be captured and no identity fix
   is claimed. This was the final compiler cycle; no retry followed.

Parent-authorized independent external linking uses the exact cycle2 objects,
the unmodified Stage2-generated entry shim copied from red-cache link inputs,
and the previously qualified canonical core-C capsule plus real backfill.
No source/object/capsule mutation, stub injection, or identity bypass occurs.
The artifact is diagnostic only, not a published/admitted capsule result.
Link succeeds, and the matrix executable exits0 with
`module-path-normalization-26-pass`. This is the native green for the exact
production function emitted by the same frozen Stage2 that produced red.

Pinned green module object SHA256:
`092ddeb91f935898841c658bf6482b5e612ef555c81a842a1b572b53dc977624`.
Fixture object: `74891fc216e2358cd0de55a4d97a462b6ae4e048c69a47320e392c077c8e055d`.
Entry shim: `81e1b049ca22def7df33d08a7a1d6c47fc7e0d046b2252186ba522102e503eb6`.
Green executable: `d42d8420080aa32fad05a1cc7a809ab553cc7880acad2e1c6010cf538b5bd96f`.
Canonical core archive: `7496e6c5e8dbfd769b1bab6c23078928f744dadd923069fa6cd80620fca2d998`.
Symbols remain module-qualified; green disassembly has no starts_with or
ends_with relocation. Link map retains exact provider ownership.

External link0.11s/RSS135921664 bytes; green run0.34s/RSS9240576 bytes.
Compared with red's run, no meaningful slowdown or memory increase is visible,
but one short run with different diagnostics is not a statistical performance
claim. Debugger RSS is separate: peak sampled tree2371408 KiB. All six watchdog
receipts have zero observer errors, quiescent cleanup and peak beneath5859375
KiB. Sampling can miss short peaks; time-l process maxima are retained too.

The corresponding SSpec has expanded negatives but is unexecuted without an
admitted general runner. No full compiler suite, MCP/LSP, bootstrap, Stage2
admission, or push PASS is claimed. Native entry/export naming policy and its
previously reviewed fix are untouched. The next canonical admission remains
the parent lane's responsibility.
