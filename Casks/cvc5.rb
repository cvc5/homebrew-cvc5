cask "cvc5" do
  version "1.3.2"

  on_macos do
    arch arm: "arm64", intel: "x86_64"
    url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-macOS-#{arch}-static.zip",
        verified: "github.com/cvc5/cvc5/releases/download/"
    sha256 arm:   "172b6ff70662184725aedf64b0189a870cc7562aca1bad9cd0ec92f682edb3af",
           intel: "b4ab528a63592da89c81eb10e35167f1e6051fd2ad8969f4e6ec54e0708fe774"
    binary "cvc5-macOS-#{arch}-static/bin/cvc5"
  end

  on_linux do
    url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-Linux-x86_64-static.zip",
        verified: "github.com/cvc5/cvc5/releases/download/"
    sha256 "1060daaf507edef9d0a68e399cfc0e9038150bccb9e2d34d081d50a7687544d2"
    binary "cvc5-Linux-x86_64-static/bin/cvc5"
  end

  name "cvc5"
  desc "Automatic theorem prover for Satisfiability Modulo Theories (SMT) problems"
  homepage "https://cvc5.github.io/"

  # Use GitHub releases to check for new versions
  livecheck do
    url :url
    strategy :github_latest
    regex(/^cvc5-(\d+(?:\.\d+)+)$/i)
  end

  postflight do
    system_command "/usr/bin/xattr",
                   args: ["-r", "-d", "com.apple.quarantine", "#{HOMEBREW_PREFIX}/bin/cvc5"],
                   sudo: false
  end

  caveats do
    license "https://github.com/cvc5/cvc5/blob/main/COPYING"
  end
end
