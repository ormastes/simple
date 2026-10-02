# Item 5 provider activation and closure architecture

Status: design update, not implemented or admitted.

## Ownership and boundaries

Compiler dependency planning owns an exact entry/runtime feature closure before
linking. Native linker adapters own target object formats, link flags, maps,
section removal and input reproduction. Provider registry owns metadata only.
Archive authority owns pinned digest/member geometry. The existing SMF provider
loader owns artifact mapping, process-callable query, invocation and lifetime.
CLI command providers own independently compiled command artifacts. Kernel and
drivers retain their current ownership; extensions do not impose ECS/MDSOC+.

Flow: entry closure -> exact native link inputs -> installed sealed provider
manifest -> metadata admission -> first-demand loader admission -> invocation
under live pins -> close after pins are released. Each transition binds the same
source/target/ABI/artifact/policy identities. Failure before activation publishes
a typed refusal and no effect. Reuse must not permit an expired/replaced authority
to bypass revalidation. In-flight owners publish one complete terminal result.

## Hot path and caches

Startup reads admitted metadata for the requested command and maps zero optional
providers. Do not scan source trees, parse provider source or spawn producer
tools on requests. First demand validates one sealed artifact and caches its
admitted identity/session; repeated demand reuses the single-flight outcome.
Exact archive digest, target, architecture, ABI, dependency interfaces and policy
generation are cache keys. Changes invalidate admission, not live owner pins;
replacement creates a new immutable generation. Failure caching records the
original typed cause and authority generation. Bounded wait exhaustion is not
permission to start a competing initializer.

## Measurable targets

Retain selected NFR-001..007: unstripped NoGC hello below 2 MiB; Linux ELF
release-small at most 15 KiB and 1.05 times matched C; non-ELF admitted fixed
format allowance; minimal interpreter startup/RSS within 10% of matched Python;
zero no-import optional loads/initializers; no unrelated demand dependencies;
30 development or 100 release samples with p50/p95 and identity products.
Record warm request latency and peak RSS as diagnostic evidence; additional
numerical request targets need user selection rather than invented budgets.

## Required design and evidence

See [current-source design](../../../05_design/compiler/perf/item5_provider_size_research_design_2026-10-02.md)
and [acceptance/TDD plan](../../../03_plan/sys_test/item5_provider_size_acceptance_2026-10-02.md).
Architecture review must reconcile actual providers, target-specific formats,
policy invalidation, startup roots and command cutover before implementation can
be certified. Historical source-token or synthetic-cohort results are auxiliary.
