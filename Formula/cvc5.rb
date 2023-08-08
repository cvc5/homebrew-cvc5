class Cvc5 < Formula
  include Language::Python::Virtualenv

  desc "Efficient open-source automatic theorem prover for SMT problems"
  homepage "https://cvc5.github.io/"
  url "https://github.com/cvc5/cvc5.git", tag: "cvc5-1.0.5"
  head "https://github.com/cvc5/cvc5.git", branch: "main"

  option "with-glp", "Permit GLP dependencies, if available"
  option "with-java-bindings", "Build Java bindings based on new C++ API"
  option "with-python-bindings", "Build python bindings based on new C++ API"

  depends_on "cmake"
  depends_on "python@3.10"

  resource "toml" do
    url "https://files.pythonhosted.org/packages/be/ba/1f744cdc819428fc6b5084ec34d9b30660f6f9daaf70eead706e3203ec3c/toml-0.10.2.tar.gz"
    sha256 "b3bda1d108d5dd99f4a20d24d9c348e91c4db7ab1b749200bded2f839ccbe68f"
  end

  resource "pyparsing" do
    url "https://files.pythonhosted.org/packages/37/fe/65c989f70bd630b589adfbbcd6ed238af22319e90f059946c26b4835e44b/pyparsing-3.1.1.tar.gz"
    sha256 "ede28a1a32462f5a9705e07aea48001a08f7cf81a021585011deba701581a0db"
  end

  def install
    venv = virtualenv_create(libexec)
    venv.pip_install resources

    command_line = [
      "./configure.sh",
      "--auto-download",
      "--static",
      "--prefix=#{prefix}",
      "-DCMAKE_FIND_FRAMEWORK=NEVER",
    ]

    command_line << "--glp" if build.with? "glp"
    command_line << "--python-bindings" if build.with? "python-bindings"
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
