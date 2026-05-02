class Simple < Formula
  desc "Simple Language Compiler and Runtime"
  homepage "https://simple-lang.org"
  version "0.3.0"

  on_macos do
    if Hardware::CPU.arm?
      url "https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-bootstrap-0.3.0-darwin-arm64.spk"
      sha256 "PLACEHOLDER_ARM64_SHA256"
    else
      url "https://github.com/simple-lang/simple/releases/download/v0.3.0/simple-bootstrap-0.3.0-darwin-x86_64.spk"
      sha256 "PLACEHOLDER_X86_64_SHA256"
    end
  end

  def install
    # Extract the SPK (tarball)
    system "tar", "-xzf", cached_download

    # Install runtime
    lib.install "lib/simple"

    # Create symlink
    bin.install_symlink lib/"simple/simple_runtime" => "simple"

    # Install documentation
    doc.install "manifest.sdn"
  end

  def caveats
    <<~EOS
      Simple Language has been installed!

      To get started:
        simple --version
        simple repl

      Documentation: https://simple-lang.org/docs
    EOS
  end

  test do
    assert_match "Simple Language v#{version}", shell_output("#{bin}/simple --version")
  end
end
