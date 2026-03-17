cask "cvc5" do
  version "1.3.3"

  on_macos do
    arch arm: "arm64", intel: "x86_64"
    url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-macOS-#{arch}-static.zip",
        verified: "github.com/cvc5/cvc5/releases/download/"
    sha256 arm:   "0ad2df5de1b35c0fda6afa9ca9f7b542a615c2137e1ec678a45deccdda1871b2",
           intel: "45e4156e9285162ae7e43504fa451ca2f618994f0d83fdd661d945f208d75f14"
    binary "cvc5-macOS-#{arch}-static/bin/cvc5"
  end

  on_linux do
    url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-Linux-x86_64-static.zip",
        verified: "github.com/cvc5/cvc5/releases/download/"
    sha256 "413f56f01f3a7374105c654581e67249eb66d4e430e748b17962d595cd4861b6"
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
