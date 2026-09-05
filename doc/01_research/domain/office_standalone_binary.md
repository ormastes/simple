# Standalone Office Binary — Domain Research

Native toolchains normally model each executable as a separate entry target.
Cargo, for example, supports multiple binary targets in one package through
`src/bin` or explicit binary target declarations. Desktop launch metadata also
separates the installed executable (`Exec`) from its discoverability check
(`TryExec`). These patterns support a cached, independently launchable Office
artifact rather than interpreting application source on every invocation.

References:

- <https://doc.rust-lang.org/stable/book/ch07-01-packages-and-crates.html>
- <https://doc.rust-lang.org/nightly/cargo/reference/cargo-targets.html>
- <https://specifications.freedesktop.org/desktop-entry/latest-single/>

For SimpleOS, a static target executable is appropriate because the guest has
no dynamic loader. Its present ring-3 terminal ABI can write serial output, but
does not provide a console-attached stdin plus working terminal mode/size
operations. A noninteractive frame launch is therefore the honest first target;
interactive TUI acceptance remains conditional on that OS ABI.
