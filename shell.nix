{ nixpkgs ? import <nixpkgs> {}
}:
with nixpkgs;
let
  coq = coq_8_9;
  coqPackages = coqPackages_8_9;
in
mkShell {
  buildInputs = [
    coq
    coqPackages.coq-ext-lib
  ];
  COQBIN = "";
  name = "extensible-nanopass-compiler";
}
