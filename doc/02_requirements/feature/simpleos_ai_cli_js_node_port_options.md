<!-- codex-research -->
# Feature Requirement Options: SimpleOS AI CLI JS/Node Port

## Option A: Contract-First Compatibility Layer

Define a SimpleOS Node-compatible API contract, CLI manifests, and hardening
SPipe specs before porting Node itself.

Pros:
- Fastest way to expose exact OS and security gaps.
- Keeps work aligned with existing SimpleOS capability and QEMU infrastructure.
- Avoids a large V8/libuv port before the required API surface is proven.

Cons:
- Does not run real upstream CLIs immediately.
- May require rework once real Node exposes deeper API expectations.

Effort: Medium.

## Option B: Bundled Node Binary First

Cross-build or package a Node binary for each QEMU target, then run bundled
Codex/Claude/Gemini CLI smoke commands on top.

Pros:
- Closest to real upstream CLI behavior.
- Quickly reveals binary/runtime gaps that contract docs may miss.

Cons:
- High risk of blocking on libc, syscalls, V8, libuv, filesystem, TLS, and
  process semantics all at once.
- Harder to isolate security failures from portability failures.

Effort: High.

## Option C: Minimal JS Agent Runtime

Implement only the JavaScript APIs needed by a small AI-CLI-compatible smoke
program, without claiming Node.js parity.

Pros:
- Smallest implementation surface.
- Lets SimpleOS prove hardened file/process/network grants early.

Cons:
- Not a true Codex/Claude/Gemini CLI port.
- Could become a parallel runtime that diverges from Node expectations.

Effort: Medium.

## Option D: SEA/Bundle-Oriented Port

Use Node single-executable or bundled CLI artifacts as the packaging model, then
port only the runtime services those bundles actually touch.

Pros:
- Avoids npm install inside SimpleOS at first.
- Produces clear package artifacts for QEMU lanes.

Cons:
- Still requires a working Node binary.
- Bundling behavior differs across CLIs and versions.

Effort: High.

## Selection Needed

Choose one option before final requirements are written. Recommended starting
point: Option A, then use its evidence to decide whether Option B or D is viable.
