cask "cvc5" do
  arch arm: "arm64", intel: "x86_64"
  os macos: "macOS", linux: "Linux"

  version "1.4.0"
  sha256 arm:          "6560851586d3aabb2a97e0c19f5f75e28da88149dc916a373debe5f2e435d71c",
         intel:        "a989c58a3acc861ad5009e1aac1fb36b12fc32a15bfebd38bc43772b6477d232",
         arm64_linux:  "724e5e218cd83d339f9993bdaf7fa0c59b9d6dcb39d4a4422177e6be82675437",
         x86_64_linux: "61d13483ec9c4e8d05c7f3d532225255b2183a0c03b161d37d942d1ba089ec6d"

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
    run "/usr/bin/xattr",
        args: ["-d", "com.apple.quarantine", "{{HOMEBREW_PREFIX}}/bin/cvc5"]
  end

  caveats do
    license "https://github.com/cvc5/cvc5/blob/main/COPYING"
  end
end
