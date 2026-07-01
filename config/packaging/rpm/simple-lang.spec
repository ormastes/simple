Name:           simple-lang
Version:        0.3.0
Release:        1%{?dist}
Summary:        Simple Language Compiler and Runtime

License:        MIT
URL:            https://simple-lang.org
Source0:        simple-bootstrap-%{version}-linux-x86_64.spk

BuildArch:      x86_64
Requires:       glibc >= 2.31

%description
The Simple programming language - a modern, fast, and expressive language
designed for clarity and productivity.

This package includes:
 - Simple runtime and compiler
 - Standard library
 - Command-line tools (REPL, compiler, checker)
 - Documentation and examples

%prep
# Extract the SPK (tarball)
tar -xzf %{SOURCE0}

%install
rm -rf %{buildroot}
mkdir -p %{buildroot}/usr/lib/simple
mkdir -p %{buildroot}/usr/bin
mkdir -p %{buildroot}/usr/share/doc/simple-lang

# Install binary
cp bin/simple_runtime %{buildroot}/usr/lib/simple/
chmod 755 %{buildroot}/usr/lib/simple/simple_runtime

# Create symlink
ln -s /usr/lib/simple/simple_runtime %{buildroot}/usr/bin/simple

# Install libraries and apps
cp -r lib/simple/* %{buildroot}/usr/lib/simple/

# Install documentation
cp manifest.sdn %{buildroot}/usr/share/doc/simple-lang/

%files
%license LICENSE
%doc README.md
/usr/bin/simple
/usr/lib/simple/simple_runtime
/usr/lib/simple/app/*
/usr/lib/simple/stdlib/*
/usr/share/doc/simple-lang/*

%post
# Create cache directory
mkdir -p /var/cache/simple
chmod 755 /var/cache/simple
echo "Simple Language installed successfully!"
echo "Run: simple --version"

%postun
if [ $1 -eq 0 ]; then
    # Remove cache on complete uninstall
    rm -rf /var/cache/simple
fi

%changelog
* Fri Jan 31 2026 Simple Language Team <team@simple-lang.org> - 0.3.0-1
- Initial RPM release
