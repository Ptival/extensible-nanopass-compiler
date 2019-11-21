{ nixpkgs ? import ~/nixpkgs {}
}:
with nixpkgs;
let
  coq-change-analytics = callPackage ~/Personal/coq-change-analytics/plugin/default.nix {};
  coqPackages          = coq-change-analytics.coqPackages;
in
mkShell {
  buildInputs = [
    coq-change-analytics
    coq-change-analytics.coqPatched
    coqPackages.InteractionTrees
  ];

  name = "extensible-nanopass-compiler";
}
