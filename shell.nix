{ nixpkgs ? import <nixpkgs> {}
}:
with nixpkgs;
mkShell {
  buildInputs = [
    coq
    coqPackages.coq-ext-lib
  ];
  COQBIN = "";
  name = "extensible-nanopass-compiler";
}
