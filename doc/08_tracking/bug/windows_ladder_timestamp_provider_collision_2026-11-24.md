# Windows ladder timestamp compatibility providers collide with Simple owners

Status: provider repair verified by retained-object native execution; formal
compiler admission and a complete new ladder run remain separate gates.

Run 45211128098, Windows rung 1 job 137819932685, source
68bb1b5d22340f9f730d37e584033793a821f0ce compiled 1612 files with zero
compilation failures. The GNU COFF link then rejected thirteen strong calendar
and progress definitions supplied by both Simple time_utils and the native-all
timestamp compatibility object. Genuine clock/TLS services pull that archive
member into the link even when Simple owns the calendar/progress API.

The repair marks only those thirteen SIMPLE_BOOTSTRAP_TIMESTAMP_COMPAT exports
weak on non-MSVC Windows. Signatures and behavior remain unchanged. Clock/TLS
providers and all other targets keep their existing ownership. No blanket
duplicate-definition suppression is added.

## Evidence

The retained seed SHA-256 is
116ca28bf3d5e8215e52391e5abdde14f2ced9d9c0e1102038cb36922224495d;
the incident native-all archive SHA-256 is
c71c014449d81f74f7c3f181e64ca5c4bc7a751ec9199899982ee2ce44c9d03b.
Artifact 14840940015 contains the actual seed, runtime and closure objects.
The incident artifact expires on 2026-12-07: the dedicated replay workflow is
an incident diagnostic, not an evergreen qualification gate or release lane.
It fails closed if evidence is unavailable or input hashes disagree.

Real local GNU COFF controls passed: compatibility-only execution of every
export; real production Simple time_utils execution with link-map ownership;
and rejection of a separate conflicting strong definition. The Simple object
was compiled from the unchanged incident source, not implemented by a test
substitute. The regression retains command lines, hashes, maps and exits.

Replacing only the timestamp archive member removes the thirteen collisions
but exposes missing process/thread services in the ladder's auto runtime
selection. The canonical successful Windows seed route uses core-c-bootstrap.
The ladder now selects that bundle only for GNU Windows seed fallback. An
actual production argv-fragment regression passes for default/GNU Windows,
MSVC Windows, Linux and Darwin; the latter three retain their previous bundle
selection. This fixture verifies dispatch only, not compiler qualification.
A separate retained-closure replay using that route's actual C supplement,
owner-member selection and existing overlap policy links and starts
simple-bootstrap 1.0.0-rc.1. Its candidate SHA-256 is
0cc0ff0865957b108c77504d30ff1ebb4b9db071759287dcf8f3ff710a7dd716.
That initial local result was provisional: version output is not native Hello
evidence.

The hosted replay derives the supplement and link command through a tiny
strict missing-extern probe, substitutes the retained compiler objects, and
requires the resulting compiler to compile and execute its own native Hello.
It does not rebuild the 1612-file closure, fabricate providers or publish a
compiler. The existing canonical supplement overlap policy is distinct from
the narrow timestamp regression, whose strong-conflict negative must fail.

Local evidence is retained under
D:/dev/simple-user-storage/build/release-bootstrap-20261123/ladder-provider-relink
and ladder-provider-regression. The live whole-suite reservation prevented a
local native Hello admission; hosted verification preserves that reservation.

## Hosted native execution

[Run 45229426680](https://github.com/ormastes/simple/actions/runs/45229426680)
passed on repair code 10430046222. Artifact 14847877532 retains all command
lines, input hashes, maps, exits and binaries. The hosted compatibility-only
and real Simple-owner checks pass; the genuine strong conflict is rejected.
The retained compiler links, starts, compiles native Hello and runs it with
exact stdout `retained-ladder-hello-ok` and exit 0. Candidate SHA-256:
2951bfd7e16ca70a375afd5ffb361b2ca05c708ad346bf382d2faa8dd6c786d1.
Hello executable SHA-256:
6f1593ce515339425e861f6b7c2f896b7b6cb5659f9a042f60ba280bafe0d6d8.
The recorded admission remains `none`: this is a real diagnostic compiler,
not a formally admitted handoff or a published release.
