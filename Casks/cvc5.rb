cask "cvc5" do
  version "1.3.0"

  on_macos do
    arch arm: "arm64", intel: "x86_64"
    url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-macOS-#{arch}-static.zip",
        verified: "github.com/cvc5/cvc5/releases/download/"
    sha256 arm:   "eb3c1a75efe28a7be7d05c4dd45846f0a7ab5cd1fcb7fb6987ebcac9164037bf",
           intel: "9bd61fbabd4786aca0c1bb63758fef56032b7e45a87880638073ec3cee7e6b2d"
    binary "cvc5-macOS-#{arch}-static/bin/cvc5"
  end

  on_linux do
    url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-Linux-x86_64-static.zip",
        verified: "github.com/cvc5/cvc5/releases/download/"
    sha256 "1e5a30c66f8fc3b65ddac69a3ac299bf03914cc58fc562e0ab6c730bf6bbfe6f"
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

  caveats do
    license "https://github.com/cvc5/cvc5/blob/main/COPYING"
  end
end
