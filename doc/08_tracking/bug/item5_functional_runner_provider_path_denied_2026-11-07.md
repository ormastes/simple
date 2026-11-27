# Item5 functional runner supplied a provider path outside admitted roots

Status: focused runner repair and failure-only staging regression prepared;
real Simple application qualification remains pending.

On `71abc0cc68789742cae2e4f7c1cc5b3f7515d505`, the canonical functional runner
staged its provider as `<output>/staged/vector-provider.so` and passed that
arbitrary absolute path to the DB and HTTP vector fixtures. Their admission
requests preserve the argument. Provider roots admit relative `build/providers/`
and the fixed system provider directories, so a normal private output path is
not admitted. See `src/os/smf/provider_loader.spl` and the composition path
checks in `src/lib/nogc_sync_mut/composition/{source,codec}.spl`.

## Repair

The runner stages the verified provider at
`<output>/build/providers/vector-provider.so`, seals the file with mode 0444
and its build directories with mode 0555, and passes the separate relative
argument `build/providers/vector-provider.so`. The absolute staged path remains
the hash authority. Existing artifact copy/hash checks are unchanged.

Both native and QEMU application command branches enter the private writable
output root. Binaries, observer, watchdog and logs remain absolute. The output
root, rather than the frozen `staged/` tree, lets the loader create its default
owner-private `.simple/provider_snapshots` directory. QEMU inherits the same
working directory and forwards the relative provider argument; its separate
target PID probe is unchanged. No provider-root rule or loader policy is relaxed.

## Verification

`scripts/check/test-item5-app-provider-path.shs` compiles a small real native C
probe and a test observer stub. It invokes the whole canonical runner with
explicitly synthetic metadata. The probe checks its actual working directory,
provider bytes/read-only mode and writable snapshot path, then deliberately
returns failure. An extracted actual `run_app` invocation additionally checks
the native vector argument. A second invocation exercises QEMU command
construction through a capture helper; no QEMU process executes. Every probe
fails deliberately and `evidence.env` must remain absent. No successful Simple
app oracle or completed functional evidence is fabricated.

The unmodified runner fails the new contract regression. The repaired runner
passes on an owned POSIX filesystem. Actual child logs and watchdog receipts
are retained under
`/root/item5-app-path-posix-regression-20261107/item5-provider-path.oGG285/`;
the bounded regression result is in
`build/review/item5-app-provider-path-regression-20261107/fixed-posix/result.json`.

An initial repaired-run attempt on this host's `/mnt/d` DrvFS mount failed
the unchanged mode assertions: a requested 0444 file appeared as 0555, and
requested 0555 directories appeared as 0777. That failure is preserved under
`build/review/item5-app-provider-path-regression-20261107/fixed/`. No assertions
were weakened and no mount policy was changed. A future qualification launcher
must verify that the chosen output filesystem honors the required staging
permissions or choose an owned POSIX output directory; a successful `chmod`
alone is not sufficient evidence on this DrvFS configuration.

This regression proves runner staging, relative argument/cwd construction and
snapshot write capability using failure-only native helpers. It does not prove
the Simple loader's execution, provider kernels, real DB/HTTP behavior, target
QEMU application execution, ISA, performance, CUDA or bootstrap readiness.
