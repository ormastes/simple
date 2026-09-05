# Loader, packed-byte, and execution-receipt integration

Base: `32eadc8b2ad947914422d7b53b131eb5c21b3eb0`

Inputs audited: `69bd3215708346faef3a879a57ba97705f69906b`, `acc98a764ac1f1e99d28180990e2f975792a02d6`.

## Integrated source owners

- `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl` — negative cache entries are authoritative, including cached empty results; uncached probes are counted and reset.
- `src/compiler/80.driver/driver_source_loading.spl` — `src/app/doc/**` remains an admissible production namespace while repository `doc/**` stays excluded.
- `src/app/cli/_CliMain/main_and_help.spl` — requested execution mode and selection fallback cross a delegated driver hop.
- `src/app/io/_CliCommands/run_commands.spl` — opt-in, single post-selection receipt for interpreter and successful SMF execution.

## Retained coherent branch owners

- Discard arena, compact routes/function headers, boxed `ModuleSurfaceParserOwner`, freeze-by-reference, and surface-array COW state are retained from the `d50ef4a..32eadc8b` ancestry.
- Stage3 directory snapshot authority and struct receiver authority already exist in the base and were not replaced by older feature-parent files.
- Existing packed-span/native byte lowering remains retained.

## Reconciled packed-byte category

The interpreter `ByteArray`/`FrozenByteArray` representation and internal byte-boundary capability are integrated across the newer value, collection, mutation, iteration, pattern, bridge, and foreign-call owners. Existing `StrBytes` text semantics, `SimplePackedSpanV1`, discard arenas, and freeze/COW owners remain intact. Generic non-byte writes widen packed storage to ordinary arrays rather than corrupting `[u8]` semantics.

Verification reached the mandatory three-cycle limit. `cargo check -p simple-compiler --lib` passed, and the final `--all-targets` cycle compiled the library but stopped on the unrelated pre-existing `m4_asan_probe` example's missing `LlvmBackend::build_m4_asan_probe_function`. The packed integration test is present but is not claimed as executed in this candidate.

## Source hashes

- loader negative cache: `bce466559dc498f3721711ae4408af66a2e7b0f2f2be53ea88a2fb7ba14af52c`
- entry closure filter: `90ab7a11faed5e1794630b927c8fc221750d0c83550d9bc62e776b9f68591ddf`
- CLI request owner: `3ac3972e8103dd6b75b420c25be0eb21712bd463a4c768b4054a595883f72b4e`
- final execution owner: `435747dd6bebec6b247f6021bf6a161fe91d7271455206b6952621744d36e1f1`
- coherent runtime memory owner: `160d5be22fe159ed35a0c0af6c0930f0ff74056750e1192a08f9ce0d62a69612`
- coherent Stage3 authority owner: `de8f8e4fa41932e679209540e22ab8828eb79e123755c203031869f3b4a1a59d`
