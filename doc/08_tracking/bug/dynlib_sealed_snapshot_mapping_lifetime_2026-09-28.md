# Sealed dynamic library snapshot is not bound through mapping retirement

Date: 2026-09-28
Status: Open
Scope: Linux exact-artifact SFFI and environment-variant native callable admission

## Current behavior and impact

`ExactArtifactDynLib.load_exact_linux` copies the requested file into a sealed
memfd, hashes `/proc/self/fd/<fd>`, loads that path, and immediately closes the
descriptor. A live mapping can then outlast its descriptor. If a later snapshot
receives the same descriptor number, it is offered to `dlopen` under the same
pathname. The dynamic loader may return the existing mapping by name before it
opens the new descriptor, so a request whose sealed bytes hash as artifact B can
receive artifact A's handle. See glibc's loaded-map name lookup in
https://sourceware.org/pipermail/glibc-cvs/2025q1/087426.html . This is a
source-backed failure mode; an admitted Linux runtime reproduction is still
required.

`dynlib_admit_exact_v1` has a separate path-swap gap: it hashes the caller's
pathname, calls `rt_host_dynlib_open` on that pathname, then hashes it again.
A swap and restore during the load window passes both hashes even though load
time code from other bytes can run. Its own comment acknowledges this limit.
The earlier SMF path race is tracked in
`provider_loader_path_digest_toctou_2026-08-16.md`.

Moving all admissions to `/proc/self/fd/<fd>` is insufficient on its own.
This changes ELF `$ORIGIN` to `/proc/self/fd`, so a provider with relative
dependencies may fail or resolve a different dependency closure. The loader
must bind that closure to the admitted evidence or explicitly refuse such an
artifact before `dlopen` runs constructors. Top-level mapped-byte identity and
dependency-closure identity are separate guarantees; proving one does not prove
the other.

## Required ownership invariant

1. Copy the source into an immutable, sealed snapshot and validate the exact
   snapshot bytes against the expected digest before any `dlopen`.
2. Give each live mapping a loader name that cannot alias a different snapshot.
   Retaining its descriptor until *confirmed final unmap* is one possible
   mechanism only when `RTLD_NODELETE`, duplicate handles, and concurrent
   retirement are accounted for. Closing the descriptor immediately after
   `dlopen`, or merely after the first `dlclose`, is not sufficient by itself.
   The current runtime has no authority that confirms final unmapping;
   successful `dlclose` alone does not establish it.
3. Keep the snapshot and mapping in one owner record. A callable use lease
   pins that record; retirement refuses new uses, waits for in-flight calls,
   closes the mapping, and releases the snapshot only when name reuse cannot
   return a previous mapping.
4. Admit the ELF dependency closure before constructors run. A self-contained
   subset may be supported first only if the loader itself verifies that
   restriction; caller-provided metadata is not evidence.
5. The exact-artifact and environment-variant APIs must share this invariant.
   Updating only one leaves the other unsafe.

## Bounded first implementation

A process-lifetime snapshot registry avoids relying on final-unmap detection.
Reserve a bounded slot before snapshot creation. Once a descriptor pathname is
offered to `dlopen`, retain that descriptor until process exit, even if the
load reports failure and loader retention is uncertain. Retire callable access
and mapping handles normally, but never recycle the descriptor number. Refuse
further admission when the registry fills. This trades bounded descriptor
retention for stable loader names. It does not by itself authenticate the
dependency closure.

For an initial self-contained ELF subset, the loader must verify the absence
of dependency-bearing metadata and unresolved dynamic imports in the sealed
bytes before `dlopen`; an unchecked caller assertion is insufficient. This
subset is an admission step toward the full Stage 6 closure requirement, not
the final general-purpose provider policy.

## Acceptance evidence

- On an admitted Linux runtime, hold artifact A callable, create artifact B
  exporting the same symbol with a different result, and load B while A is
  live. Both calls must return their own result and be tied to their respective
  digests, including a forced descriptor-number reuse attempt.
- Replace the pathname between pre-load inspection and admission. No code from
  a nonmatching artifact may run, including an ELF constructor.
- Retire a callable while one call is in flight; the call completes from its
  original mapping and a stale copy refuses a new call. For the bounded first
  implementation, its descriptor remains reserved until process exit; a full
  reclamation implementation needs an authority proving final unmapping.
- A provider with `$ORIGIN`/relative dependencies is either admitted with a
  verified closure or refused before `dlopen`; there is no silent fallback to
  ambient host libraries.

Until these checks pass, neither path can claim exact mapped-byte identity for
hostile-writer admission. This blocks Stage 6/6A promotion in
`doc/03_plan/compiler/environment_optimized_dynamic_libraries.md`.
