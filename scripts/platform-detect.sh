#!/bin/sh
# Platform detection — sourced by bootstrap scripts.
# Sets: PLATFORM_TRIPLE, PLATFORM_ARCH, PLATFORM_OS

PLATFORM_ARCH="$(uname -m)"
case "$(uname -s)" in
  Linux)   PLATFORM_OS="linux"   ;;
  Darwin)  PLATFORM_OS="macos"   ;;
  FreeBSD) PLATFORM_OS="freebsd" ;;
  MINGW*|MSYS*|CYGWIN*) PLATFORM_OS="windows" ;;
  *)       PLATFORM_OS="unknown" ;;
esac

case "${PLATFORM_ARCH}" in
  x86_64|amd64) PLATFORM_ARCH="x86_64" ;;
  aarch64|arm64) PLATFORM_ARCH="aarch64" ;;
  riscv64) PLATFORM_ARCH="riscv64" ;;
esac

case "${PLATFORM_OS}" in
  linux)   PLATFORM_TRIPLE="${PLATFORM_ARCH}-unknown-linux-gnu" ;;
  macos)   PLATFORM_TRIPLE="${PLATFORM_ARCH}-apple-darwin" ;;
  freebsd) PLATFORM_TRIPLE="${PLATFORM_ARCH}-unknown-freebsd" ;;
  windows) PLATFORM_TRIPLE="${PLATFORM_ARCH}-pc-windows-msvc" ;;
  *)       PLATFORM_TRIPLE="${PLATFORM_ARCH}-unknown-${PLATFORM_OS}" ;;
esac

export PLATFORM_TRIPLE PLATFORM_ARCH PLATFORM_OS
