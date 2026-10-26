# Native authority issuer archive lacks the startup entry

Status: OPEN. Native execution and cache-authority qualification remain blocked.
Bug DB reconciliation is pending; this report is the provisional bug record.

The Phase 1 bootstrap compiler produced a real AMD64 archive from the frozen
149-module canonical source-authority closure. Compilation reported 149 compiled,
zero reused, and zero failed. Strict linking then failed on one undefined symbol:
`__simple_main`, referenced by the already qualified `simple_entry.obj` startup.
No executable was produced or run. This is an entry-generation or build-interface
problem to diagnose, not evidence that the source-authority implementation passed.

Subsequent actual `llvm-nm --defined-only` inspection found a defined `spl_main`
symbol in this archive. The archive therefore has an entry, but it does not match
the `__simple_main` name expected by the selected self-hosted startup. Investigate
the canonical Phase 1 startup ABI and its existing generated template first;
do not manufacture a symbol alias or claim that all entry generation is absent.

## Actual evidence

- Producer SHA-256: `d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`.
- Private input commit: `02f691a2844b8e23bce4981a5888f9d23d5cc261`.
- Archive: `build/native_probe/compiler-source-authority-20261013-astra/native-issuer-v2/attempt1/artifact/native_authority_issuer.lib`.
- Archive SHA-256: `1d958d4400ac1cc2e7cf49c597caefe8244e33cbcf8229e350adb5702a3dcbbb`.
- Compile receipt: `41f114b467b5055c830103ec58f35e296a0237b23a993457af20c217ed32d3fc`.
- Link result: `build/native_probe/compiler-source-authority-20261013-astra/native-issuer-link-v1/attempt1/RESULT.json`.
- Link result SHA-256: `fb72edd3fe37d77a1a8857be61fae758e075fd52b5b1fdb43c0cb6176ead0ec7`.
- Link receipt SHA-256: `68ad7df5524c52164dd7fc9b6f9b2da42ef04df242e9ae5077eca7397f9712b8`.

Both attempts reached Job 0 and retained unchanged source/tool input pins. The
link exited 1 in 0.617 seconds. No unresolved-symbol suppression, fabricated
runtime globals, entry alias, or alternate startup was applied.

## Repair and acceptance

The Astra compiler lane must establish the actual emitted entry symbols and the
canonical archive/startup ABI before changing the entry source or compiler.
Preserve the existing compatible module cache; rebuild only affected inputs
where the cache owner can prove that reuse is valid. Do not rewrite identity
stamps to claim reuse.

Acceptance requires a strict link with the canonical entry ABI, PE/map evidence
that the entry comes from the intended source, and a separately qualified native
source-authority smoke test. Add a regression for archive entry preservation and
for an entry importing canonical dependencies. A compile-only exit 0 or archive
header does not satisfy these criteria.

## Corrected strict link

The changed startup input resolved the link error without recompiling any of
the 149 modules. The second strict link used the original Phase 1 generated
`_main_stub.o`, SHA-256
`6ef11d1ffe268e4d74ccbb2fa69d4569f1eb1b0c795137b9f5940dc601e7b0f5`,
whose C source matches the frozen canonical MSVC template, and selected
`wmainCRTStartup` instead of `mainCRTStartup`. It exited 0 and reached Job 0.

The map binds `spl_main` to the actual issuer archive's `mod_148.o` and
`__simple_call_module_inits` to that archive's `_init_all.o`. The runtime
initialization, shutdown, and wide-argument providers come from the qualified
core-C runtime. No startup fallback was selected. Executable SHA-256:
`c14924c2839436cbec76d15745be969a99c97ddadcc8dfcb1edb34fae6273b2c`.
Receipt SHA-256:
`2587e6f12e716e944c01dd5f06caafe33f162e44dd2b6ac4571a316a85964781`.

The frozen result retains its failed literal `sys_get_args` symbol witness.
A separate addendum establishes the actual LLVM lowering to `rt_get_args`,
the issuer object's undefined reference, and the map's real runtime provider;
the original result was not rewritten or the passing link repeated. Native
argument behavior and canonical source-authority issuance remain unrun, so
the helper is not yet qualified for downstream compiler or cache admission.

## Subsequent native smoke and selector repair

The earlier unrun statement above records the strict-link review point. The
same executable subsequently passed the real portable-project canonical issuer
smoke in 2.412 seconds, exit 0 and Job 0. All eight published authority fields,
the nine-source snapshot, generation and forwarded arguments were inspected.
Result SHA-256: `786dd53b448dc134f1d940f29523b0e6a2d339c0df48e48d8ae6b8cfc0bcf6ae`.
Receipt SHA-256: `db99aff11bf37ee958193ebf073215656f09bc263f1b3776a07ab72e322b97c2`.
This qualifies that issuer operation, not the downstream compiler: the portable
receiver failed HIR with unresolved `print_raw` and also reported an invalid
array handle during parsing. No tool archive was produced.

The original helper's fixed `src` selector could not admit the genuine test
fixture under `test/fixtures/lib`. A private selector repair retains the original
fixture and uses canonical source acquisition for `src/lib` plus
`test/fixtures/lib`. Its first compile reused 148 modules and rebuilt one,
with zero failed modules, in 9.942 seconds overall. Archive SHA-256:
`da9d23f2abcc46743d74a3f821aecaaa951ae1effa3149843b8eeae6fb67c2fb`.
Result SHA-256: `e8b3473cbf08cdc520949bac2127e7b4aae1430f3cb6558ec7fec9b5c323401c`.
Receipt SHA-256: `eaa52d26f0549a367c5bea213953fc1072a75f3a43a3cc357168ed92b029d9b2`.
This is compile/archive evidence only; the changed selector executable still
requires strict linking and actual positive and negative native tests. No
six-product or 0.1-second compilation claim follows from these results.

The selector archive subsequently strict-linked successfully in 0.663 seconds
with unchanged inputs and Job 0. All eleven entry, initializer, runtime and
fallback map checks passed. New executable SHA-256:
`302c9c3345bae94c5bcfd2ac569701eabaedf37151b8ba6dc6023cce96488d80`.
Result SHA-256: `d6a2ecaedb182b65466376538002af39dd183f0b366e61ff24fd14a58e5afb34`.

Actual native negative validation covered eleven rejection criteria, including
duplicate/overlapping roots, traversal, absent or uncovered roots, malformed
options and an actual directory ending in `.spl`. The first suite had ten
passes and one expected-label mismatch: the absent-root command hit the usage
guard before the source-count guard. Its result remains unchanged. Only that
case was revised to satisfy usage arity and rerun; it passed with the expected
source-count diagnostic and no authority publication. Ten green cases were not
replayed. Results: `4feb787d1502c32888eec822055a5f805ed8ced0625b1b30ed3e1c29e5812041`
and `9dd0d9aaa097d1e5ea9c68b94d8bd5d487f4499f5a9c44393db6076b896994b8`.
Both reached Job 0 without source/input drift. Positive issuance for the original
8,659-file test project remains a separate acceptance criterion; no six native
test product has yet been qualified.
