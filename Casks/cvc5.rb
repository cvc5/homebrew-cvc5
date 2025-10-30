cask "cvc5" do
  version "1.3.1"

  on_macos do
    arch arm: "arm64", intel: "x86_64"
    url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-macOS-#{arch}-static.zip",
        verified: "github.com/cvc5/cvc5/releases/download/"
    sha256 arm:   "a0e7f5b03b1bc4284fbfff7cdfb08c704801701cf7ece83a13f8a505e7581215",
           intel: "e7fe4af9491bd7c0db7591c0a483775735bd1a98b23933fd337a73ae39c10ff9"
    binary "cvc5-macOS-#{arch}-static/bin/cvc5"
  end

  on_linux do
    url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-Linux-x86_64-static.zip",
        verified: "github.com/cvc5/cvc5/releases/download/"
    sha256 "1a1cda20d2df4938fa4944a69f33ddc9172e319ece0eed0aa09c4d7abede3ed1"
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
