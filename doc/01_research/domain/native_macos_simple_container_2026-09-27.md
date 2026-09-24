<!-- codex-research -->
# Native macOS Simple Container: domain findings

Apple's App Sandbox restricts a macOS app through signed entitlements. A
sandboxed app may embed a command-line helper that inherits its sandbox; the
entitlements and actual sandbox state must be checked. Apple creates an app
container directory for sandboxed apps. This is a macOS-native process route,
not a Linux namespace container and not a per-workload filesystem namespace.

Sources: [App Sandbox](https://developer.apple.com/documentation/security/app-sandbox),
[protecting data and embedded tools](https://developer.apple.com/documentation/security/protecting-user-data-with-app-sandbox),
[configuring App Sandbox](https://developer.apple.com/documentation/xcode/configuring-the-macos-app-sandbox).

Apple's `container` project executes Linux workloads in lightweight VMs. It
does not satisfy a request to run a macOS program directly on a Mac host.
[Apple Containerization](https://github.com/apple/containerization).

Design inference: use the existing Simple Container identity/lifecycle
contract for both macOS and SimpleOS. Keep the macOS signed helper, native
process lease, entitlement verification, and actual exit with the macOS
provider; keep scheduler task authority and kernel exit with SimpleOS. A
shared App Sandbox bundle does not by itself isolate two workloads from each
other, so initial Mac admission must be single-workload or explicitly scoped
to trusted same-owner workloads until per-attempt isolation is proven.

Further boundary (2026-09-28): Apple's embedded-tool guidance describes a
child that inherits its containing app's sandbox; it does not give each child
an independent container or prove that a child cannot detach. The hosted
Process Observation V4 schema reserves `POV4_CAP_EXACT_TREE`, and its current
host provider does not advertise that capability. Its supported leader-only
observation therefore cannot prove the required no-child/cleanup property for
an untrusted native workload. This is a design inference from the Apple
inheritance contract and the in-repo capability definition, not a claim that
App Sandbox itself failed on an unrestricted Mac.

Sources: [embedding a command-line tool](https://developer.apple.com/documentation/xcode/embedding-a-helper-tool-in-a-sandboxed-app),
[App Sandbox inheritance](https://developer.apple.com/library/archive/documentation/Miscellaneous/Reference/EntitlementKeyReference/Chapters/EnablingAppSandbox.html).

2026-09-28 Astra follow-up: Apple DTS explains that a child already inheriting
its parent's sandbox can trap if it is signed to install a fresh sandbox;
`com.apple.security.inherit` requests inheritance instead. Our ad-hoc CLI and
`.app` probes aborted before `main`, and a further CLI signed with both
entitlements also aborted. No matching crash report was accessible, so the
cause of these local aborts remains unconfirmed. Inheritance would share this
session's existing policy and cannot qualify a separate container.
[Apple DTS on sandbox inheritance](https://developer.apple.com/forums/thread/679940).

An independently launched signed app or XPC/launchd service is a candidate
for normal unprivileged macOS deployment. It needs an authenticated request
channel and live sandbox verification; launch from this restricted session
cannot serve as that proof. Apple's NSRunningApplication identity guidance
warns against using PID alone, and launchd's documented cleanup covers the
same process group, which a detaching descendant can leave. These APIs do not
prove cleanup of arbitrary children. The current rootless design must keep
untrusted arbitrary-program admission blocked until a stronger exact-tree
authority is selected and verified.
[independent service discussion](https://developer.apple.com/forums/thread/786363),
[NSRunningApplication process identity](https://developer.apple.com/documentation/appkit/nsrunningapplication/processidentifier).
