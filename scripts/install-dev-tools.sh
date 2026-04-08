#!/usr/bin/env bash
set -Eeuo pipefail

export DEBIAN_FRONTEND=noninteractive

OS="$(uname -s)"
echo "Detected OS: $OS"

# ============================================================================
# Package installation
# ============================================================================

if [ "$OS" = "Linux" ]; then
    echo "[1/5] apt update"
    sudo apt-get update -qq

    echo "[2/5] install packages"
    sudo apt-get install -y \
      bash coreutils findutils grep sed gawk tree less \
      git patch diffutils ripgrep fd-find \
      jq bat \
      curl wget unzip zip p7zip-full tar xz-utils \
      make cmake ninja-build clang lld pkgconf python3 python3-pip \
      htop lsof strace procps psmisc net-tools \
      fzf shellcheck silversearcher-ag universal-ctags \
      || true

    # yq, eza, delta may not be in default repos
    sudo apt-get install -y yq eza git-delta 2>/dev/null || true

elif [ "$OS" = "FreeBSD" ]; then
    echo "[1/5] pkg update"
    sudo pkg update -f

    echo "[2/5] install packages"
    sudo pkg install -y \
      bash coreutils findutils gnugrep gsed gawk tree less \
      git patch diffutils ripgrep fd-find \
      jq bat \
      curl wget unzip zip \
      gmake cmake ninja llvm pkgconf python3 \
      htop lsof sudo \
      fzf the_silver_searcher universal-ctags \
      || true

    # FreeBSD-specific extras (may not be in default repos)
    sudo pkg install -y go-yq eza git-delta 2>/dev/null || true

else
    echo "Unsupported OS: $OS"
    exit 1
fi

# ============================================================================
# Compatibility symlinks
# ============================================================================

echo "[3/5] create compatibility symlinks"
mkdir -p "$HOME/.local/bin"

# Ubuntu ships fd as fdfind
if command -v fdfind >/dev/null 2>&1 && ! command -v fd >/dev/null 2>&1; then
    ln -sf "$(command -v fdfind)" "$HOME/.local/bin/fd"
fi

# Ubuntu often ships bat as batcat
if command -v batcat >/dev/null 2>&1 && ! command -v bat >/dev/null 2>&1; then
    ln -sf "$(command -v batcat)" "$HOME/.local/bin/bat"
fi

# FreeBSD grep/sed are different — create g-prefixed aliases if needed
if [ "$OS" = "FreeBSD" ]; then
    for tool in grep sed awk; do
        if command -v "g${tool}" >/dev/null 2>&1; then
            ln -sf "$(command -v "g${tool}")" "$HOME/.local/bin/${tool}"
        fi
    done
fi

# ============================================================================
# PATH and aliases
# ============================================================================

echo "[4/5] ensure ~/.local/bin is on PATH"
shell_rc=""
if [ -n "${ZSH_VERSION-}" ] || [ -f "$HOME/.zshrc" ]; then
    shell_rc="$HOME/.zshrc"
else
    shell_rc="$HOME/.bashrc"
fi

touch "$shell_rc"

if ! grep -Fq 'export PATH="$HOME/.local/bin:$PATH"' "$shell_rc"; then
    {
        echo ''
        echo '# user-local tool shims'
        echo 'export PATH="$HOME/.local/bin:$PATH"'
    } >> "$shell_rc"
fi

echo "[5/5] add safe interactive aliases"
if ! grep -Fq '# claude-friendly aliases' "$shell_rc"; then
    {
        echo ''
        echo '# claude-friendly aliases'
        echo 'alias rg="rg --hidden --glob !.git"'
        echo 'alias ll="ls -alF"'
        echo 'alias la="ls -A"'
        echo 'alias l="ls -CF"'
        echo ''
        echo 'if command -v bat >/dev/null 2>&1; then'
        echo '  alias cat="bat --paging=never"'
        echo 'fi'
        echo ''
        echo 'if command -v eza >/dev/null 2>&1; then'
        echo '  alias ls="eza"'
        echo '  alias ll="eza -al --group-directories-first"'
        echo '  alias la="eza -a --group-directories-first"'
        echo '  alias lt="eza --tree --level=2"'
        echo 'fi'
        echo ''
        echo 'if command -v delta >/dev/null 2>&1; then'
        echo '  git config --global core.pager delta >/dev/null 2>&1 || true'
        echo '  git config --global interactive.diffFilter "delta --color-only" >/dev/null 2>&1 || true'
        echo 'fi'
    } >> "$shell_rc"
fi

echo ""
echo "Done. OS=$OS"
echo "Open a new shell or run: source \"$shell_rc\""
echo ""
echo "Installed tools:"
echo "  rg, grep, fd, jq, bat, delta, git, curl, cmake, ninja, clang, strace, lsof, fzf, shellcheck, ctags"
echo ""
echo "Notes:"
echo "  - grep was NOT replaced with rg"
echo "  - find was NOT replaced with fd"
echo "  - safe shims: fd->fdfind, bat->batcat (Linux), g{grep,sed,awk} (FreeBSD)"
