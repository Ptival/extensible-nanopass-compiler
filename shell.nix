{ nixpkgs ? import <nixpkgs> {}
}:
with nixpkgs;
mkShell {
  buildInputs = [
    coq
    coqPackages.coq-ext-lib
  ];
  name = "extensible-nanopass-compiler";
}
