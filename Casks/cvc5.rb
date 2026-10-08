cask "cvc5" do
  arch arm: "arm64", intel: "x86_64"
  os macos: "macOS", linux: "Linux"

  version "1.4.2"
  sha256 arm:          "24397f7d022e755876ca836193d4c5f9c1d4326f0f6c01f7d7fc1ddd6bc5096c",
         intel:        "f2bbbfe089c77c4a676dd05f262eee86b9718c32374c424138c416024ff42477",
         arm64_linux:  "765ebee59d9e5efccb60a445fa66fbddfb07a8de9fe7a5b6d128e5c2aafec974",
         x86_64_linux: "7eb18f8c814c36a46c5a7d003983e9cfbc4b0a9828d6dd596239291bd4cc61d8"

  url "https://github.com/cvc5/cvc5/releases/download/cvc5-#{version}/cvc5-#{os}-#{arch}-static.zip"
  name "cvc5"
  desc "Automatic theorem prover for Satisfiability Modulo Theories (SMT) problems"
  homepage "https://cvc5.github.io/"

  # Use GitHub releases to check for new versions
  livecheck do
    url :url
    strategy :github_latest
    regex(/^cvc5-(\d+(?:\.\d+)+)$/i)
  end

  binary "cvc5-#{os}-#{arch}-static/bin/cvc5"

  postflight_steps do
    on_macos do
      run "/usr/bin/xattr",
          args: ["-d", "com.apple.quarantine", "{{HOMEBREW_PREFIX}}/bin/cvc5"]
    end
  end

  caveats do
    license "https://github.com/cvc5/cvc5/blob/main/COPYING"
  end
end
