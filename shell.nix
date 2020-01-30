{ nixpkgs ? import <nixpkgs> {}
}:
with nixpkgs;
mkShell {
  buildInputs = [
    coq_8_9
    coqPackages_8_9.coq-ext-lib
  ];
  COQBIN = "";
  name = "extensible-nanopass-compiler";
}
