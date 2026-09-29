cask "cvc5" do
  arch arm: "arm64", intel: "x86_64"
  os macos: "macOS", linux: "Linux"

  version "1.4.1"
  sha256 arm:          "9d43271585ef33a477c79069ca0d5b02af585cafc1a2388d1cd612e00f459f9f",
         intel:        "1da9916d5d9b8f2c02100b72026b39111b49b4992ce96e30b3bc079abb816070",
         arm64_linux:  "0939d2c47612391af49b6113edeef92352f46839f6b16cb2521eaf7c673cbc82",
         x86_64_linux: "2f8efe58fe27ba7bccbb504533f690b9312d69da14192712460e4a19231f02a1"

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
