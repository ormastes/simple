# Phase3 requested-object evidence through batch65

Status: **incomplete**. The frozen inventory contains **2,249** compiler modules. Through batch65, **2,213** unique modules were actually started: **446 PASS, 1,726 FAIL, and 41 interrupted**. **36 remain untried**. Selections that never started are not attempts. Prior successful, failed and interrupted requests were excluded from subsequent dispatches.

These verdicts concern requested module objects produced by the retained compiler. They do not establish a rebuilt full Phase3 compiler, a Phase4 tool executable, or any of the six required native test products. The separately observed native Hello chain is independent evidence and does not turn these module objects into a full compiler qualification.

## Terminal delta and provenance

Batch64 added13 unique failures. Batch65 then added22 unique completed requests: **1 PASS and21 FAIL**, with no new interrupted requests. Both outer collectors terminated exit0 with final Job active count0; coordinator exit0 does not mean every module compiled successfully.

Batch65 used three actual workers under80 configured credits. Each worker retained the16GiB scheduling forecast; the lane reservation was52,076,478,464 bytes, including512MiB controller overhead. The original180s per-module and1200s outer deadlines, bounded logs/storage, exclusive claims, and observer-only RSS policy remained in effect. No claim of80 simultaneously active workers or native speedup follows.

The new verified requested object is `src/compiler/10.frontend/core/types.spl`: **203,166 bytes**, SHA256 `0839e7d05984b452896183d8bacce6cf9910ec2430aaccaf86298f234ea87c1a`. Its AMD64 COFF header and section bounds were checked against the actual bytes. The source identity, requested-object hash, child log and terminal Job receipt were bound to its result.

The producer remained SHA256 `f2ce31b4e4dea1ea6ca3e8726cd411144914c24ffcf58722021f38c4b6393dec`, with frozen source manifest `bb003c6170066d540d65b094f580c00dcdcb849079101212c35b133c3bacda7a`. Later source changes do not modify or qualify this producer. Compatible caches and earlier artifacts were preserved; no identity stamps were rewritten.

## Sealed evidence

Local evidence packet: `build/native_probe/phase3-aggregate-through65-20261013-astra/`.

| Artifact | SHA256 |
|---|---|
| `SUMMARY.json` | `dbb0f90334cd5a30c85172dde41292823c10f70c5cbcad249b8d26d65c0b5178` |
| `B65_ROWS.json` | `a4b720b979f236cade974b1e7d2075565c3738702b404a9cdc9c89b82c59fb22` |
| `NEW_COFF_SUCCESS_SEALS.json` | `860e1c884af7d57ea6b720243a7f4092a0306c96e8884da7f36ec68be81967d5` |
| `NEXT_UNTRIED_MANIFEST.json` | `fefb2b7780808f7d4543b0fae1a493c04aa2e0b3eec12c603fe0a80d241628b8` |
| Batch65 outer receipt | `0769d4e9f81f3d371773f3798d7ec9ae18966bfc8a2a092ed37fe2ec5abfa4c8` |

The new aggregate chains to the sealed through63 inventory and batch64 delta. It validates batch65's22 new claims/results, child Job closures, log/source identities and new COFF, without repeating old green tests or recounting old object files. The first new reader stopped before publishing because it used the wrong receipt directory; the corrected reader follows the retained helper's sibling `*-logs` directory and preserves all validation gates. No compiler was rerun for that correction.

## Separate exported-scalar prerequisite: HOLD

An independent Phase4 strict link retained a real reference to `WINDOWS_REDIRECTED_TOKEN_BASE` without a matching provider definition. The physical provider object exists. A private source-owner diagnostic investigated trailing-export scalar visibility using actual frozen parser/HIR/MIR owners; no manual HIR, fake global, alias or production patch was introduced.

Cycle1's retained output showed the trailing-export scalar as `exported=true`, `private=true`, with0 storage slots and a named failure. Its explicit-public control showed1 storage slot and a named PASS. The canonical30s child timeout prevented a completed three-case verdict; the attempt terminated exit5/Job0 and remains HOLD. Receipt: `8ce22909e8ef82e60bfa668bfbf1962dcc07309923e8082fa57339aa87478e65`.

Cycle2 executed only the previously uncompleted private control, retaining the exact helper and case body. It produced `exported=false`, `private=true`, slots0 and one named PASS, exit0/Job0. However, the trusted reader reported `trunc=true`; the strict result therefore remains HOLD. Receipt: `68268d098c3fc3324770bc97a6ebf82a140448afaf21118bf26c96844ddcb8ae`. These are observations from separate bounded processes, not a fabricated combined three-case PASS. The public control was not replayed.

Both diagnostics observed all six designated owner files, with no outside reads or changed source pins. Reading owners does not prove every dispatched method binding, and the private entry lacks consumed-byte tracing. No native compiler repair or complete source qualification is claimed. The original Phase4 archive also emitted an independent invalid-array runtime diagnostic and remains unqualified. A static audit found real wrapper relocations to all four qualified initializer bodies; their exclusion from prefix-based startup discovery alone does not establish missing initialization.

At this report boundary, batch65 and both scalar diagnostics are terminal. Batch66 is prepared from the36 never-started entries and remains **unlaunched pending review and fresh resource admission**. No unverified source patch is included in this report.
