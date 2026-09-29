# Verified SimpleOS image CLI V1

`simple os image` composes one new x86_64 NVFS carrier through
`simpleos_verified_image_compose_v1`. All artifacts, sizes, and manifest
identities are explicit. The command does not build missing inputs. It rejects
duplicate, unknown, missing, oversized, or unsafe options before opening files.

```text
simple os image --show-plan \
  --target=x86_64-unknown-simpleos \
  --root=/absolute/trusted/staging --output=system.img --sectors=32768 \
  --profile=dev --build-id=build-2026-09-14 --source-id=source-commit-id \
  --sosix-version=sosix-v1 --kernel=kernel.elf --init=init.smf \
  --loader=loader.smf --selector=selector.smf --compiler=simple.smf
```

Replace the example paths and identities with the intended build inputs.
The kernel must be a loadable x86_64 ELF executable. Init, loader, selector,
and any compiler must be canonical x86_64 SimpleOS SMF executable payloads.
Every artifact path and the output path is relative to the trusted absolute
root; all must be distinct. Existing output leaves are never overwritten.
Parent directories must already exist. The size is bounded to 8–32768 sectors
(512 bytes each); capacity and filesystem materialization still have to succeed.

`--profile` accepts `dev`, `runtime`, and `minimal`. `--compiler` is optional
and accepted only for `dev`. A dev image without a compiler is descriptive
composition output and cannot satisfy compiler-in-guest qualification. Manifest
identities use the existing canonical lowercase identity grammar; the CLI does
not infer a source commit, version, profile, or artifact location.

`--show-plan` validates input shape and prints an explicitly unqualified plan.
It opens no artifact or output. Remove it to execute composition. Values also
accept the `--name value` form. `simple os image --help` lists every option.

Successful execution writes the existing canonical, length-framed
`SimpleOsImageManifestV1` encoding to stdout followed by a single newline. This
is not SDN and is not a release receipt. A consumer must remove the CLI's final
newline before hashing canonical bytes. No separate manifest sidecar is created
by the command; redirect stdout to a fresh path outside the artifact/output set
if a copy is needed. A nonzero exit means stdout is diagnostic text and must
never be admitted as a manifest.

The owner derives artifact and carrier hashes from the read bytes, validates the
persisted NVFS namespace, publishes the new image durably, reads back its exact
identity, and closes retained root authority before returning the manifest.
Failures after publication can leave an output whose admission was not completed;
inspect that path before retrying. The command does not claim firmware boot,
compiler execution, reboot persistence, signing, or release readiness.

The native retained-root provider currently supports hosted Linux with the
required `openat2` and `O_TMPFILE` operations. Unsupported hosts, kernels,
filesystems, and freestanding runtimes fail closed through the provider. No
pathname I/O fallback is used. An admitted self-hosted CLI containing the new
provider is required for production execution; source/spec coverage is not
runtime qualification.
