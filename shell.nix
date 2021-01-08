{ sources ? import ./nix/sources.nix {}
, nixpkgs ? import sources.nixpkgs {}
}:
with nixpkgs;
let
  coqPackages = coqPackages_8_12;
in
mkShell {
  buildInputs = [
    coqPackages.coq
    coqPackages.coq-ext-lib
  ];
  COQBIN = "";
  name = "extensible-nanopass-compiler";
}
