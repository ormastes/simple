# Quick Installation Guide

Choose your platform:

## Linux

```bash
curl -fsSL https://install.simple-lang.org/bootstrap.sh | sh
```

Or install via package manager:

**Ubuntu/Debian:**
```bash
sudo apt-get install simple-lang
```

**Fedora/RHEL:**
```bash
sudo dnf install simple-lang
```

## macOS

```bash
brew install simple-lang/tap/simple
```

Or use the quick installer:
```bash
curl -fsSL https://install.simple-lang.org/bootstrap.sh | sh
```

## Windows

Download the installer from [Releases](https://github.com/simple-lang/simple/releases):
- [simple-lang-0.3.0-x86_64.msi](https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-lang-0.3.0-x86_64.msi)

Or use Chocolatey:
```powershell
choco install simple-lang
```

---

## Verify Installation

```bash
simple --version
# Output: Simple Language v0.3.0
```

---

## Quick Start

```bash
# Start REPL
simple repl

# Run a script
echo 'print "Hello, Simple!"' > hello.spl
simple run hello.spl

# Compile a program
simple compile hello.spl -o hello
./hello
```

---

## Full Documentation

See [doc/guide/installation.md](doc/guide/installation.md) for detailed installation instructions, troubleshooting, and platform-specific information.

---

## Package Sizes

- **Bootstrap** (runtime only): ~6 MB
- **Full** (with source): ~250 MB

---

## System Requirements

- **OS**: Linux (kernel 4.4+), macOS 10.13+, Windows 10+
- **CPU**: x86_64 or ARM64
- **RAM**: 256 MB minimum, 1 GB recommended
- **Disk**: 50 MB minimum, 1 GB recommended

---

## Building from Source

```bash
git clone https://github.com/simple-lang/simple.git
cd simple
cd rust && cargo build --profile release-opt
cd .. && make install
```

See [BUILDING.md](BUILDING.md) for detailed build instructions.

---

## Support

- 📖 [Documentation](https://simple-lang.org/docs)
- 🐛 [Issues](https://github.com/simple-lang/simple/issues)
- 💬 [Discord](https://discord.gg/simple-lang)
- 📧 [Email](mailto:support@simple-lang.org)
