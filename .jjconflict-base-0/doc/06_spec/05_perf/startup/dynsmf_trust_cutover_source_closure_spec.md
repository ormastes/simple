# dynSMF trust cutover startup source-closure specification

## Purpose

This executable specification protects the production startup cutover from
adding trust-registry work to the empty, help, or version paths and from
reintroducing path-based or legacy dynamic loading after admission.

## Primary flow

1. `src/app/main.spl` parses and returns from empty, help, and version commands.
2. Only a non-fast-path command loads `simple_dynsmf_trust.sdn` through the
   OS-owned `src/os/smf/dynsmf_trust_registry.spl` owner.
3. The registry binds exact library id, path, ABI, artifact kind, ordered export
   set, interface/module ABI, and SHA-256 identity.
4. Ordinary and component startup receive the retained admitted byte image;
   neither reopens an artifact path in its registry branch.

## Failure behavior

Missing, malformed, ambiguous, or identity-mismatched trust configuration is a
typed fail-closed result. Compatibility entry points without an admitted
registry remain non-authoritative and cannot publish a dynamic handle.

## Performance and closure checks

The executable source-closure gate asserts that the OS trust owner imports no
app/compiler module, launches no process, and scans no directory. It also
asserts that registry admission occurs textually after the empty/help/version
returns and that the hard `--` terminator remains owned by the canonical option
router.

## Executable source

`test/05_perf/startup/dynsmf_trust_cutover_source_closure_spec.spl`

## Evidence command

```sh
SIMPLE_LIB=src <diagnostic-simple> test test/05_perf/startup/dynsmf_trust_cutover_source_closure_spec.spl --mode=interpreter --fail-fast
```

The diagnostic binary identity and exit status must be retained with the run.
This gate is source/interpreter evidence only; it is not Stage 4, bootstrap,
native performance, release, or cross-host evidence.
