# Global Content-Addressed Cache — Audit & Architecture Selection

**Date:** 2026-07-24
**Audited revision:** `main` @ `11a84de4150af18c2bd4b5760e5ace705f4b68bd`
**Selection:** **Option C** (hybrid path-stamp index + SHA-256 CAS + dependency-aware
action keys) as the default architecture, with **Option A** (strict rehash-everything)
implemented as C's strict verification mode. B is an explicitly-unsafe local turbo mode;
D is a later evolution; E is rejected.

---

## 1. Does Simple currently use a global cache?

No — not in the strong sense (reusable across sessions/threads/processes, keyed by
content + all semantic inputs, safe under source/compiler/macro/aspect/option/dependency
change). Several caches exist; none is a unified persistent content-addressed cache.

| Current layer | Scope & key | Safe global cache? |
|---|---|---|
| Rust interpreter module cache | `thread_local!` maps keyed by normalized module path | No — one thread/process; path-based |
| Interpreter path-resolution cache | `thread_local!`, bare `u64` hash of import parts / base dir / SIMD tier | No — process/thread-local; FS changes unrepresented |
| Self-hosted `load_session_cache.spl` | module-level dicts keyed by module name / current file / source path | No — session data; no indexed production caller |
| SMF mmap cache | `SmfCache` per JIT/loader, keyed by path | No — per-loader, not cross-process |
| Loaded SMF modules / JIT symbols | per `ModuleLoader`, keyed by path + symbol | No — holds executable addrs + runtime lifecycle |
| Native-build disk cache | persistent compiler-scoped build cache | Yes for its own lane — but separate from interpreter loading |

The Rust interpreter cache stores **evaluated runtime `Value`s and function defs with
captured defining-module environments** — not merely parsed syntax. It must NOT be moved
verbatim into a process/disk-global map.

**Safe to globalize (once immutable + correctly keyed):** source blobs, tokens/immutable
ASTs, interface summaries, pure macro-definition summaries + pre-hygiene templates,
HIR/MIR with stable IDs and no process pointers, SMF bytes + strict metadata, read-only
mmaps of immutable CAS files, dependency manifests + action-result records.

**Must remain session-local (phase 1):** evaluated exports, env/mutable globals/global
snapshots, closures + captured envs, function-owner/overload registries, deferred imports
+ circular-import state, macro injection queues, class context, gensym state, runtime AOP
registries + proceed closures, executable addresses/relocated pages/JIT mappings/refcounts.

## 2. Current SMF status

Stale-stub failure is mitigated: runner rejects missing SMFs, files < 256 B, and SMFs
older than source; resolver order is `.spl` → package source → `.shs` → `.smf`; the
producer that left source-adjacent interrupted SMFs was moved to temp output. So the
resolver does **not** generally prefer `.smf` over `.spl`.

But the runner check is explicitly a cheap size/mtime prefilter — "not a real SMF header
parse." It cannot prove the SMF was built from current source bytes / compiler impl /
macro defs / AOP selection / dependency interfaces / backend-target-runtime-feature
config. **Keep it a prefilter, not the global-cache trust boundary.**

## 3. Macro handling — caching hole

Rust macro contract cache is keyed only by `macro_name`; definition-time preprocessing
reads the current env/function/class tables then skips when the bare name is cached. Two
modules can define the same macro name with different contracts, scopes, visible
symbols, shadowing, or imported compile-time defs → false reuse. The cached result also
carries introduced funcs/classes/fields/injection blocks/runtime `Value`s — not wholly
immutable.

**Fix — two layers:**
- **Pure macro-definition cache**, keyed by `MacroDefinitionDigest = SHA256(domain,
  defining_module_stable_id, canonical_definition_AST, engine_schema_version,
  compiler_identity, sorted_compile_time_read_set_interface_digests)`. Result holds only
  immutable info (validated contract, declared introductions, injection labels/anchors,
  return-type metadata, pre-hygiene template).
- **Macro-invocation cache**, keyed by `MacroInvocationDigest = SHA256(
  MacroDefinitionDigest, canonical_arg_ASTs, evaluated_const_args, target_cfg_and_features,
  lexical_scope_interface_digest, declared_compile_time_inputs)`.
- **Hygiene:** prefer caching a pre-hygiene template + applying fresh gensym IDs per
  call-site; alternatively include a stable invocation-site ID + hygiene seed in the key.
- Macros reading undeclared files/env/time/randomness/network/mutable-compiler-state →
  **uncacheable**; declared reads hash into the invocation key.

## 4. AOP handling

Compiled before/after advice is woven as a **symbolic MIR call** to the advice name (body
not inlined at weave). General `around` stays on the interpreter/runtime path (proceed
closure built at runtime); certain security plans do materialize runtime calls into MIR.
So: advice-body-only change with unchanged interface → caller need not be re-woven, but
the linked/loaded image must still bind the new impl. LTO/inlining is the exception.

**Four AOP identities:**
- `AopSelectionDigest` — pointcut rules, advice form, priority/order, matcher version,
  target name/sig, attributes/scope/effects/join-point class, AOP config + enabled state.
- `AdviceInterfaceDigest` — symbol identity, param/return types, calling convention,
  effects/caps, visibility, ABI/layout.
- `AdviceImplementationDigest` — exact advice body / compiled artifact identity.
- `AopLinkPlanDigest` — ordered selected advice symbols, their impl artifact IDs,
  static-reloc vs runtime-lookup mode, required runtime-support version.

**Invalidation:** woven caller depends on `AopSelectionDigest` + `AdviceInterfaceDigest`;
final linked/loaded image depends on selected impl artifacts. Advice signature/effects/
ABI/pointcut/form/priority/matcher/target-surface changes → re-weave + relink; body-only
→ relink/rebind only; LTO/security-plan → re-weave (impl embedded).

**Dependency-discovery hole:** seed interpreter applies aspects only to entry-module
functions; imported-module aspects/targets aren't fully collected. A future global cache
must include the **complete applicable aspect-set digest**, else it serves artifacts built
before a newly-applicable aspect existed. Fix direction: collect advice from all loaded
modules, apply to imported-module calls.

## 5. Verified caching holes

| Pri | Hole | False-hit cause | Correction |
|---|---|---|---|
| P0 | Interp module cache keyed only by normalized path | hit before source reread; source/compiler/dep/macro/aspect change invisible | session realization keyed by full action digest; global cache only immutable artifacts |
| P0 | Selective clear retains stdlib + path-resolution state | long-lived daemon keeps old stdlib def after file change | validate retained entries vs source/action digest |
| P0 | Path-resolution cache stores only `u64` + caches negatives | create/delete/rename + higher-priority candidates change resolution; hash collision undisambiguable | store full typed key + resolution witness + directory generation |
| P0 | Macro contracts cached by bare name | same-name / changed-context reuse | qualified stable macro ID + definition/read-set digest |
| P0 | SMF mmap + loaded-module caches path-keyed | replacing bytes at same path → "already loaded" | resolve path → immutable `ArtifactId`; compare IDs |
| P0 | Semantic validation not on normal load hit path | records exist without controlling reuse | mandatory action-manifest verification before admission |
| P0 | Macro/AOP deps not fully discovered | new applicable macro/aspect affects output but absent from old dep list | record semantic read sets + aspect-selection roots |
| P1 | Old SMFs with zero options hash accepted | unknown producer/options enter trusted cache | local compat input only; rebuild before global admission |
| P1 | `validated_smf_load` takes `source_path` but doesn't validate content | name implies validation it lacks | compare stored source SHA/action digest to input |
| P1 | Semantic combined hash is small custom text hash; dep keys unsorted | unfit as global identity | SHA-256 over canonical sorted binary encoding |
| P1 | Self-hosted load-session invalidation omits target/freshness | stale resolution/freshness after invalidate | generation-aware entries or invalidate all related indexes |
| P1 | Library SMF extraction via `/tmp/smf_getter_<module>.smf` | same-name collision / stale exposure | in-memory reader or digest-qualified private temp |
| P1 | Some disk cache paths flatten `/`→`_` | distinct sources → same filename | digest paths or escaped structured components |

**Resolution witness** (closes "new file appears"): per import record ordered candidate
paths probed, existence result per higher-priority candidate, selected candidate,
parent-dir generation/digest, resolver policy/version. (ccache direct-mode manifest has
the same limitation — hashing known headers can't discover a newly-appearing header
unless FS lookup state is represented.)

## 6. Options considered

| Opt | Design | Safety | Perf | Best fit | Failure mode |
|---|---|---|---|---|---|
| A strict SHA-256 CAS | rehash all inputs every lookup | highest practical | med | CI/bootstrap/release/forensic | repeated read+hash |
| B metadata/watcher | trust path/inode/size/mtime/watcher | low–med | highest | explicit local turbo only | timestamp races, missed events, NFS, stale negatives |
| **C hybrid stamp + CAS + action graph** | reuse known SHA when strong stamp/gen unchanged, else rehash; artifacts always SHA/action-addressed | high | high | **recommended default** | more complexity; still needs complete dep discovery |
| D red-green query engine | every query records real deps + stable fingerprint | high, precise | highest warm | long-term arch | large retrofit |
| E process-global evaluated map | move exports/env into global concurrent map | unsafe | fast | none | cross-session mutable leakage, false hits |

**A's real limit is missing inputs, not the hash** — a perfect SHA over an incomplete
input list is still unsafe. **C** avoids re-hashing unchanged files while keeping a strict
SHA-backed artifact identity, with A as its verification mode. Evidence C's cost is
tolerable: native-build compiler-identity already hashes a `path|size|sha256` manifest of
2,933 files in ~90–100 ms — fine for strict mode, avoided per-load by the stamp index.

Underlying model follows Bazel / LLVM CAS: immutable content store + action cache mapping
complete input identity → output identities.

## 7. Selection

**C as default architecture; A as C's strict verification mode.** B = explicitly-unsafe
local acceleration only. D = later evolution after cache identity / dependency manifests /
session-vs-global boundary are correct. **E rejected.**

Implementation plan: see
`doc/03_plan/compiler/cache/global_cas_interpreter_cache_option_c_plan_2026-07-24.md`.
