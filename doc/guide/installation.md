# Installation Guide

This guide covers all installation methods for the Simple Language compiler and runtime.

## Table of Contents

- [Quick Install](#quick-install)
- [Platform-Specific Installation](#platform-specific-installation)
  - [Linux](#linux)
  - [macOS](#macos)
  - [Windows](#windows)
- [Manual Installation](#manual-installation)
- [Building from Source](#building-from-source)
- [Verification](#verification)
- [Troubleshooting](#troubleshooting)

---

## Quick Install

### Linux and macOS

The fastest way to install Simple:

```bash
curl -fsSL https://install.simple-lang.org/bootstrap.sh | sh
```

Or with a custom installation directory:

```bash
SIMPLE_INSTALL_DIR=/opt/simple curl -fsSL https://install.simple-lang.org/bootstrap.sh | sh
```

### Windows

Download the installer from [Releases](https://github.com/simple-lang/simple/releases) and run:

```powershell
simple-bootstrap-0.3.0-windows-x86_64.exe
```

---

## Platform-Specific Installation

### Linux

#### Ubuntu/Debian

**Option 1: APT Repository (Recommended)**

```bash
# Add Simple repository
curl -fsSL https://packages.simple-lang.org/gpg | sudo gpg --dearmor -o /usr/share/keyrings/simple-lang.gpg
echo "deb [signed-by=/usr/share/keyrings/simple-lang.gpg] https://packages.simple-lang.org/deb stable main" | sudo tee /etc/apt/sources.list.d/simple-lang.list

# Install
sudo apt-get update
sudo apt-get install simple-lang
```

**Option 2: Download .deb Package**

```bash
# Download
wget https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-lang_0.3.0_amd64.deb

# Verify checksum
sha256sum -c simple-lang_0.3.0_amd64.deb.sha256

# Install
sudo dpkg -i simple-lang_0.3.0_amd64.deb
sudo apt-get install -f  # Fix dependencies if needed
```

**Uninstall:**

```bash
sudo apt-get remove simple-lang        # Remove package
sudo apt-get purge simple-lang          # Remove package + config
```

#### Fedora/RHEL/CentOS

**Option 1: DNF/YUM**

```bash
# Add Simple repository
sudo dnf config-manager --add-repo https://packages.simple-lang.org/rpm/simple-lang.repo

# Install
sudo dnf install simple-lang
```

**Option 2: Download .rpm Package**

```bash
# Download
wget https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-lang-0.3.0-1.x86_64.rpm

# Verify checksum
sha256sum -c simple-lang-0.3.0-1.x86_64.rpm.sha256

# Install
sudo rpm -i simple-lang-0.3.0-1.x86_64.rpm
```

**Uninstall:**

```bash
sudo dnf remove simple-lang
```

#### Arch Linux

```bash
# Using yay (AUR)
yay -S simple-lang

# Or manually
git clone https://aur.archlinux.org/simple-lang.git
cd simple-lang
makepkg -si
```

#### Generic Linux (Tarball)

```bash
# Download bootstrap package
wget https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-bootstrap-0.3.0-linux-x86_64.spk

# Extract to ~/.local
mkdir -p ~/.local
tar -xzf simple-bootstrap-0.3.0-linux-x86_64.spk -C ~/.local

# Add to PATH
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc

# Verify
simple --version
```

### macOS

#### Homebrew (Recommended)

```bash
# Install
brew install simple-lang/tap/simple

# Verify
simple --version
```

#### Manual Installation

**Apple Silicon (M1/M2/M3):**

```bash
# Download
curl -LO https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-bootstrap-0.3.0-darwin-arm64.spk

# Verify checksum
shasum -a 256 -c simple-bootstrap-0.3.0-darwin-arm64.spk.sha256

# Extract
tar -xzf simple-bootstrap-0.3.0-darwin-arm64.spk -C ~/.local

# Add to PATH
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.zshrc
source ~/.zshrc
```

**Intel (x86_64):**

```bash
# Download
curl -LO https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-bootstrap-0.3.0-darwin-x86_64.spk

# Extract and install (same as above)
tar -xzf simple-bootstrap-0.3.0-darwin-x86_64.spk -C ~/.local
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.zshrc
source ~/.zshrc
```

**Uninstall:**

```bash
# Homebrew
brew uninstall simple

# Manual
rm -rf ~/.local/lib/simple ~/.local/bin/simple
```

### Windows

#### MSI Installer (Recommended)

1. Download `simple-lang-0.3.0-x86_64.msi` from [Releases](https://github.com/simple-lang/simple/releases)
2. Double-click to run the installer
3. Follow the installation wizard
4. The installer will automatically add Simple to your PATH

#### Chocolatey

```powershell
# Install
choco install simple-lang

# Verify
simple --version
```

#### Manual Installation (PowerShell)

```powershell
# Download
Invoke-WebRequest -Uri "https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-bootstrap-0.3.0-windows-x86_64.spk" -OutFile "simple-bootstrap.spk"

# Extract
tar -xzf simple-bootstrap.spk -C "$env:LOCALAPPDATA\Simple"

# Add to PATH (User)
$path = [Environment]::GetEnvironmentVariable("Path", "User")
[Environment]::SetEnvironmentVariable("Path", "$path;$env:LOCALAPPDATA\Simple\bin", "User")

# Restart terminal and verify
simple --version
```

**Uninstall:**

- Via MSI: Control Panel → Programs → Uninstall Simple Language
- Via Chocolatey: `choco uninstall simple-lang`
- Manual: Delete `%LOCALAPPDATA%\Simple` and remove from PATH

---

## Manual Installation

For all platforms, you can manually install from the bootstrap package:

### 1. Download Bootstrap Package

Download the appropriate package for your platform:

- **Linux x86_64**: `simple-bootstrap-0.3.0-linux-x86_64.spk`
- **macOS ARM64**: `simple-bootstrap-0.3.0-darwin-arm64.spk`
- **macOS x86_64**: `simple-bootstrap-0.3.0-darwin-x86_64.spk`
- **Windows x86_64**: `simple-bootstrap-0.3.0-windows-x86_64.spk`

### 2. Verify Checksum

```bash
# Linux/macOS
sha256sum -c simple-bootstrap-VERSION-PLATFORM.spk.sha256

# Windows (PowerShell)
(Get-FileHash simple-bootstrap-VERSION-PLATFORM.spk -Algorithm SHA256).Hash -eq (Get-Content simple-bootstrap-VERSION-PLATFORM.spk.sha256)
```

### 3. Extract

```bash
# Linux/macOS (user-local)
tar -xzf simple-bootstrap-VERSION-PLATFORM.spk -C ~/.local

# Linux/macOS (system-wide)
sudo tar -xzf simple-bootstrap-VERSION-PLATFORM.spk -C /usr/local

# Windows
tar -xzf simple-bootstrap-VERSION-PLATFORM.spk -C "$env:LOCALAPPDATA\Simple"
```

### 4. Configure PATH

**Linux/macOS (bash):**

```bash
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

**Linux/macOS (zsh):**

```zsh
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.zshrc
source ~/.zshrc
```

**Linux/macOS (fish):**

```fish
fish_add_path ~/.local/bin
```

**Windows (PowerShell):**

```powershell
$path = [Environment]::GetEnvironmentVariable("Path", "User")
[Environment]::SetEnvironmentVariable("Path", "$path;$env:LOCALAPPDATA\Simple\bin", "User")
```

### 5. Verify Installation

```bash
simple --version
# Output: Simple Language v0.3.0
```

---

## Building from Source

### Prerequisites

- **Rust**: 1.75+ (install from [rustup.rs](https://rustup.rs))
- **Git**: Any recent version
- **Build tools**:
  - Linux: `build-essential` (Ubuntu/Debian) or `base-devel` (Arch)
  - macOS: Xcode Command Line Tools (`xcode-select --install`)
  - Windows: Visual Studio Build Tools

### Build Steps

```bash
# Clone repository
git clone https://github.com/simple-lang/simple.git
cd simple

# Build optimized runtime
cd rust
cargo build --profile release-opt

# Run tests (optional)
cargo test --workspace

# Build bootstrap package
cd ..
./scripts/build-bootstrap.sh

# Install locally
make install
# Or system-wide
sudo make install-system
```

### Development Build

```bash
# Quick development build
cd rust
cargo build

# Run tests
make test

# Run linter
make lint

# Format code
make fmt
```

---

## Verification

After installation, verify that Simple is working correctly:

### Basic Verification

```bash
# Check version
simple --version
# Output: Simple Language v0.3.0

# Check installation location
which simple
# Output: /home/user/.local/bin/simple (or similar)
```

### REPL Test

```bash
# Start REPL
simple repl

# Try some commands
>>> print "Hello, Simple!"
Hello, Simple!

>>> val x = 42
>>> x * 2
84

>>> :quit
```

### Run a Script

Create a test file `hello.spl`:

```simple
fn main():
    print "Hello, World!"
    val nums = [1, 2, 3, 4, 5]
    val doubled = nums.map(\x: x * 2)
    print "Doubled: {doubled}"
```

Run it:

```bash
simple run hello.spl
# Output:
# Hello, World!
# Doubled: [2, 4, 6, 8, 10]
```

---

## Troubleshooting

### Command Not Found

**Problem:** `simple: command not found`

**Solution:**

1. Verify installation directory:
   ```bash
   ls ~/.local/bin/simple
   ```

2. Check PATH:
   ```bash
   echo $PATH
   ```

3. Add to PATH if missing:
   ```bash
   export PATH="$HOME/.local/bin:$PATH"
   ```

4. Reload shell configuration:
   ```bash
   source ~/.bashrc  # or ~/.zshrc
   ```

### Permission Denied

**Problem:** `Permission denied` when running simple

**Solution:**

```bash
# Fix permissions
chmod +x ~/.local/bin/simple
chmod +x ~/.local/lib/simple/simple_runtime
```

### Library Not Found (Linux)

**Problem:** `error while loading shared libraries`

**Solution:**

```bash
# Update library cache
sudo ldconfig

# Or set LD_LIBRARY_PATH
export LD_LIBRARY_PATH="$HOME/.local/lib:$LD_LIBRARY_PATH"
```

### macOS Security Warning

**Problem:** "simple_runtime cannot be opened because the developer cannot be verified"

**Solution:**

```bash
# Remove quarantine attribute
xattr -d com.apple.quarantine ~/.local/lib/simple/simple_runtime

# Or allow in System Preferences
# System Preferences → Security & Privacy → General → "Allow Anyway"
```

### Windows Antivirus Blocking

**Problem:** Windows Defender or antivirus blocks installation

**Solution:**

1. Add exception for Simple installation directory
2. Download from official sources only
3. Verify checksums before installing

### Version Mismatch

**Problem:** Old version still showing after upgrade

**Solution:**

```bash
# Clear shell hash cache
hash -r

# Or restart terminal
```

### Uninstall Issues

**Problem:** Files remain after uninstall

**Solution:**

```bash
# Manual cleanup (Linux/macOS)
rm -rf ~/.local/lib/simple
rm ~/.local/bin/simple
rm -rf ~/.config/simple
rm -rf ~/.cache/simple

# Manual cleanup (Windows)
Remove-Item -Recurse -Force "$env:LOCALAPPDATA\Simple"
Remove-Item -Recurse -Force "$env:APPDATA\Simple"
```

---

## Next Steps

After installation:

1. **Read the Tutorial**: [Getting Started Guide](getting_started.md)
2. **Browse Examples**: `doc/examples/`
3. **Check Documentation**: `doc/guide/`
4. **Join Community**: [Discord](https://discord.gg/simple-lang) | [Forum](https://forum.simple-lang.org)

---

## Package Sizes

| Package Type | Platform | Compressed | Installed |
|--------------|----------|------------|-----------|
| Bootstrap    | Linux    | ~6 MB      | ~15 MB    |
| Bootstrap    | macOS    | ~6 MB      | ~15 MB    |
| Bootstrap    | Windows  | ~7 MB      | ~18 MB    |
| Full         | All      | ~250 MB    | ~500 MB   |

---

## System Requirements

### Minimum

- **OS**: Linux (kernel 4.4+), macOS 10.13+, Windows 10
- **RAM**: 256 MB
- **Disk**: 50 MB (bootstrap), 1 GB (full)
- **CPU**: x86_64 or ARM64

### Recommended

- **OS**: Ubuntu 20.04+, macOS 12+, Windows 11
- **RAM**: 1 GB
- **Disk**: 2 GB
- **CPU**: x86_64 or ARM64, 2+ cores

---

## Support

Need help?

- **Documentation**: https://simple-lang.org/docs
- **Issues**: https://github.com/simple-lang/simple/issues
- **Discord**: https://discord.gg/simple-lang
- **Email**: support@simple-lang.org
