# Waiting for upstream merge for coqPackages_8_11.coq-ext-lib
{ nixpkgs ? import ~/personal/nixpkgs {}
}:
with nixpkgs;
let
  coqPackages = coqPackages_8_11;
in
mkShell {
  buildInputs = [
    coqPackages.coq
    coqPackages.coq-ext-lib
  ];
  COQBIN = "";
  name = "extensible-nanopass-compiler";
}
