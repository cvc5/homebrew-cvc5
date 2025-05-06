cask "cvc5" do
  arch arm: "arm64", intel: "x86_64"

  version "1.2.1"
  sha256 arm:   "18e0bd283d44f720f72bf80175169ef63e985628b7ba1502aaf812f57f981461",
         intel: "bdde9557bbb9b812af270c3f418836c285957b3ed81385b87428d2d595ffbf47"

  url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-macOS-#{arch}-static.zip",
      verified: "github.com/cvc5/cvc5/releases/download/"
  name "cvc5"
  desc "Automatic theorem prover for Satisfiability Modulo Theories (SMT) problems"
  homepage "https://cvc5.github.io/"

  # Use GitHub releases to check for new versions
  livecheck do
    url :url
    strategy :github_latest
    regex(/^cvc5-(\d+(?:\.\d+)+)$/i)
  end

  binary "cvc5-macOS-#{arch}-static/bin/cvc5"

  caveats do
    license "https://github.com/cvc5/cvc5/blob/main/COPYING"
  end
end
