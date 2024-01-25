class Cvc5 < Formula
  include Language::Python::Virtualenv

  desc "Efficient open-source automatic theorem prover for SMT problems"
  homepage "https://cvc5.github.io/"
  url "https://github.com/cvc5/cvc5.git", tag: "cvc5-1.1.1"
  head "https://github.com/cvc5/cvc5.git", branch: "main"

  option "with-java-bindings", "Build Java bindings based on new C++ API"

  depends_on "cmake" => :build
  depends_on "python@3" => :build
  depends_on "gmp"
  depends_on :java if build.with? "java-bindings"

  resource "tomli" do
    url "https://files.pythonhosted.org/packages/c0/3f/d7af728f075fb08564c5949a9c95e44352e23dee646869fa104a3b2060a3/tomli-2.0.1.tar.gz"
    sha256 "de526c12914f0c550d15924c62d72abc48d6fe7364aa87328337a31007fe8a4f"
  end

  resource "pyparsing" do
    url "https://files.pythonhosted.org/packages/37/fe/65c989f70bd630b589adfbbcd6ed238af22319e90f059946c26b4835e44b/pyparsing-3.1.1.tar.gz"
    sha256 "ede28a1a32462f5a9705e07aea48001a08f7cf81a021585011deba701581a0db"
  end

  def install
    venv = virtualenv_create(buildpath/"venv", "python3")
    venv.pip_install resources

    command_line = [
      "./configure.sh",
      "--auto-download",
      "--static",
      "--prefix=#{prefix}",
      "-DPython_EXECUTABLE=#{buildpath}/venv/bin/python",
    ]

    command_line << "--java-bindings" if build.with? "java-bindings"

    command = Shellwords.join(command_line)
    system "bash", "-c", "export CMAKE_PREFIX_PATH=#{libexec}:$CMAKE_PREFIX_PATH; #{command}"

    chdir "build" do
      system "make", "install"
    end
  end

  test do
    (testpath/"test.smt2").write <<~EOS
      (set-logic QF_UF)
      (declare-const |Hello World!| Bool)
      (assert (not |Hello World!|))
      (check-sat)
    EOS

    result = shell_output "#{bin}/cvc5 #{testpath/"test.smt2"}"
    assert_match(/sat/, result)
  end
end
