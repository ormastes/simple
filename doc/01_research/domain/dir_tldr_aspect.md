<!-- claude-research 2026-11-01; from model knowledge, no live web fetch this session -->
# dir_tldr_aspect: Domain Research

## AspectJ: pointcuts and compile, binary, and load-time weaving
- Pointcuts are composable predicates (`execution`, `call`, `within(pkg..*)`, `@annotation`,
  `&&`/`||`/`!`). `within` is a scope designator, which corresponds to a directory scope here.
- There are three weave modes: compile-time (ajc), binary (post-compile), and load-time (an
  LTW agent driven by `aop.xml`). With LTW, one aspect artifact applies to many packages and
  `aop.xml` supplies the scope. This is the precedent for "same plugin, different dir matcher".
- ajc incrementality: an aspect change re-weaves every type it *could* match. It uses
  per-type crosscutting summaries (shadow munger lists). Lesson: re-match against per-scope
  join-point summaries, not sources.

## Spring AOP: proxies
- `Advisor` = `Pointcut` (`ClassFilter` + `MethodMatcher`, split into static and dynamic
  matching) + `Advice`. Small composable interfaces are an OOP authoring model that is easy
  to change.
- Self-invocation bypasses advice and there is a runtime proxy cost. Take the OOP authoring
  model, but weave at compile time.

## Bazel / Buck2: per-package actions
- The unit is the package (directory). Actions are keyed by an input digest, and the action
  cache plus CAS give reuse regardless of path when the inputs are relative. Persistent
  workers keep a tool resident across actions, which is the precedent for a resident dir TLDR.
- Buck2 DICE and Salsa use early cutoff: dependants stop when a recomputed value's digest is unchanged.

## rustc / clang: module summaries
- rustc `.rmeta` enables pipelining, because dependants start on metadata before codegen. The
  query system uses red/green marking.
- clang modules (PCM/BMI) and ThinLTO per-module summaries plus a thin-link index both read a
  small summary before heavy work. This matches "check the dir TLDR first".
- The summary must be signatures-only and cheap, or it delays the first object. Pipelining
  is the model for the first-`.o` ≤10 s rule.

## Incremental invalidation via summaries
- Negative facts must be summarised too (the macro RR absence family; the dir membership root
  for added files).
- Content-addressed identity (Nix/Bazel): reuse comes from digests of *normalised* inputs.
  Path normalisation (relative paths, matcher passed as a parameter) enables cross-package reuse.

## Hardening prior art
- Fail closed: an invalid or missing cache entry is a miss, never a success (Bazel).
- Determinism: sorted inputs, no timestamps, hermetic tools (reproducible-builds.org).
- Plugin security: digest-pinned toolchains (Bazel), dependency verification (Gradle), and
  WASM/WASI capability sandboxing for untrusted plugins.
