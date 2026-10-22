# macOS App Sandbox local probe

Scope: ad-hoc signing only; source, entitlements, app bundle, and binaries were
first created under `/private/tmp`. The probe itself made no repository edits
and ran no Simple tests.

The signing inputs and a corrected version of the probe source are preserved as
`test/fixtures/native_macos_simple_container/{probe.c,sandbox.entitlements.plist,Probe.Info.plist}`
for an unrestricted Mac host replay. This is a platform probe, not the Simple
Container implementation or a production helper.

Commands (directory abbreviated as `$P`):

```sh
P=/private/tmp/codex-appsandbox-probe.tSj1g1
xcrun clang "$P/probe.c" -o "$P/probe"
"$P/probe" /Users/ormastes/simple/AGENTS.md /etc/hosts
/usr/bin/codesign --force --sign - --identifier org.simple.codex.sandboxprobe --entitlements "$P/entitlements.plist" "$P/probe"
/usr/bin/codesign --verify --strict --verbose=2 "$P/probe"
"$P/probe" /Users/ormastes/simple/AGENTS.md /etc/hosts
```

Baseline printed `started`, then `ALLOWED` for both paths. Signed helper signature verified (`valid on disk`, `satisfies its Designated Requirement`), but launch exited 134 without stdout/stderr. Entitlements inspection confirmed only `com.apple.security.app-sandbox=true`.

A second controlled variant copied the executable to `Probe.app/Contents/MacOS/Probe` and supplied `Contents/Info.plist` with CFBundleIdentifier, CFBundleExecutable, CFBundlePackageType=APPL, and CFBundleVersion. Commands:

```sh
/usr/bin/codesign --force --sign - --entitlements "$P/entitlements.plist" "$P/Probe.app"
/usr/bin/codesign --verify --strict --verbose=2 "$P/Probe.app"
```

Python `subprocess.run` launched the bundled binary with the same two path arguments: returncode=-6 (SIGABRT), empty stdout and stderr. Signature verification passed.

Attempting `/usr/bin/log show --last 3m --style compact --predicate 'eventMessage CONTAINS "org.simple.codex.sandboxprobe" OR (process == "Probe") OR (process == "probe")' --info` returned `log: Cannot run while sandboxed`. Existing diagnostic reports predated this probe and were not treated as evidence.

Conclusion: signing works, but independent App Sandbox launch is unverified in the current already-restricted execution context. Host-file denial is NOT proven. No sandbox-exec or sandbox bypass was used. No inference that ad-hoc App Sandbox cannot work outside this execution context is justified.

Apple sources:

- [Embedding a command-line tool](https://developer.apple.com/documentation/xcode/embedding-a-helper-tool-in-a-sandboxed-app): inherited helpers require sandbox and inherit entitlements; documents ad-hoc signing.
- [Apple DTS explanation](https://developer.apple.com/forums/thread/679940): child processes inherit parent sandbox; enabling a new sandbox can conflict, while inherit preserves parent policy.
- [Accessing files](https://developer.apple.com/documentation/security/accessing-files-from-the-macos-app-sandbox): limited filesystem access, containers, and user-selected access mechanisms.

The inherited-helper configuration would not establish a new narrower boundary around the worker; it was therefore not used as a substitute for the requested independent isolation proof.

Follow-up diagnostic: a copy signed with both `com.apple.security.app-sandbox`
and `com.apple.security.inherit` verified its entitlements, then also exited
134 before `main`. No matching crash report was accessible. Apple DTS describes
a specific nested-sandbox trap, but these local exits do not establish that
as their cause.

The replay fixture now emits fixed `OPEN_STATUS` records. Only `EACCES` or
`EPERM` counts as denial; `ENOENT` and other failures count as errors. The
script requires the unsigned control to read the same canonical sentinel
before and after signed runs. This corrects the original probe's broad
`DENIED` label and substring acceptance risk.

## Replay on an unrestricted Mac login

Run `scripts/check/check-native-macos-simple-container-sandbox.shs
HOST_SENTINEL_FILE` from an unrestricted Mac login using a non-sensitive file
outside the app container. The script compiles the preserved C fixture,
confirms the unsandboxed control can read the sentinel, ad-hoc signs and
verifies both CLI and `.app` forms, then requires an actual signed launch and
host-file denial. A zero exit is only a candidate: separately record the
running process sandbox status, explicitly provisioned workspace access,
native workload exit, and cleanup. A pre-`main` abort or inherited parent
sandbox cannot qualify the independent Mac route.
