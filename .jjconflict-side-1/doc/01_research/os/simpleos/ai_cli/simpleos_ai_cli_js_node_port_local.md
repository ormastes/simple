<!-- codex-research -->
# Domain Research: AI CLI JS/Node Port

## Current CLI Packaging Signals

- OpenAI Codex CLI is distributed through npm as `@openai/codex`; OpenAI's
  help article describes global npm installation and API-key authentication.
  Source: https://help.openai.com/en/articles/11096431
- The current npm page for `@openai/codex` also points to npm installation,
  Homebrew installation, and GitHub release binaries. The npm result observed
  on 2026-05-30 showed active release churn, so exact version pinning must be
  captured at implementation time. Source:
  https://www.npmjs.com/package/@openai/codex
- Anthropic Claude Code is distributed as `@anthropic-ai/claude-code`; the
  official setup docs list Node.js 18+ and npm global installation. Source:
  https://docs.anthropic.com/en/docs/claude-code/setup
- Google Gemini CLI is distributed as `@google/gemini-cli`; the npm/docs search
  result observed on 2026-05-30 lists Node.js 20+ and TypeScript-to-JavaScript
  bundled CLI artifacts. Sources:
  https://www.npmjs.com/package/@google/gemini-cli and
  https://google-gemini.github.io/gemini-cli/docs/releases.html

## Node.js Portability Signals

- Node.js depends on V8 and libuv-style OS integration. For SimpleOS this means
  the hard part is not JavaScript syntax; it is the OS substrate: filesystem,
  event loop, timers, networking, TLS, process spawning, stdio/TTY, signals,
  module loading, package resolution, crypto, and credential storage.
- Node.js official build documentation identifies Linux x64 and arm64 as
  primary supported binary targets, armv7 as experimental in recent releases,
  and platform/toolchain constraints such as kernel/libc baselines. Source:
  https://github.com/nodejs/node/blob/main/BUILDING.md
- Node.js Single Executable Applications can package a JavaScript application
  with a Node binary, but still require a working Node binary and the expected
  OS APIs at runtime. Source:
  https://nodejs.org/api/single-executable-applications.html
- Unofficial Node builds include riscv64 and linux-x86 variants, which is useful
  evidence for feasibility but not a SimpleOS support guarantee. Source:
  https://github.com/nodejs/unofficial-builds

## Security Implications For AI CLIs

- AI coding CLIs require broad local capabilities: file reads/writes, shell
  commands, process control, network API calls, terminal control, and secret
  access. On SimpleOS these must map to explicit capability grants rather than
  ambient POSIX-like authority.
- Package installation from npm creates a supply-chain boundary. SimpleOS should
  prefer pinned package manifests, checksums, and offline provisioning for QEMU
  validation lanes.
- A single-executable or bundled CLI path can reduce npm-at-runtime complexity,
  but does not remove the need for Node-compatible OS services.

## Domain Conclusion

The lowest-risk path is to start with a Node-compatible host contract and
manifested CLI smoke programs, then graduate to a real Node/V8/libuv port or a
bundled Node binary only after SimpleOS proves the required OS services and
capability denials in QEMU.

## 2026-05-30 Bun Architecture Check

The active hardening goal asks for a Node.js-like and Bun-like JavaScript
engine while keeping Simple's MDSOC+ architecture. Current Bun documentation
describes Bun as an all-in-one JavaScript/TypeScript toolkit with a single
dependency-free binary that includes runtime, package manager, test runner, and
bundler. Bun's runtime documentation says it uses JavaScriptCore under the hood
and that its transpiler/runtime are written in Zig.

Useful Bun lessons for SimpleOS:

- keep the developer-facing tool surface cohesive: script runner, package
  manifest reader, bundle/transpile path, and test smoke runner should be one
  runtime profile rather than scattered host shell wrappers;
- treat TypeScript/JSX/transpile/package behavior as part of the runtime
  contract, not as ad hoc pre-build behavior;
- keep Node compatibility explicit and measurable because Bun's own docs call
  Node compatibility an ongoing effort;
- support WebAssembly as a first-class loader/runtime concern, with validation
  and import binding before execution.

SimpleOS should not copy Bun's internal architecture directly. Bun's Zig plus
JavaScriptCore design is not the requested MDSOC+ shape and is not portable to
SimpleOS QEMU targets without a large host-engine port. The aligned path is a
Simple-owned JS runtime capsule with Bun-like tool cohesion, explicit
Node-compatible OS surfaces, fail-closed capability gates, and a browser/WASM
contract shared by Simple browser, host WM, SimpleOS WM, Android, and iOS.

Sources:

- https://bun.sh/docs
- https://bun.sh/docs/runtime
- https://bun.sh/docs/runtime/transpiler
- https://bun.sh/docs/test
