{ pkgs ? import <nixpkgs> { } }:
let
  agda = pkgs.agda.withPackages (ps: [
    ps.standard-library
  ]);
in
pkgs.mkShell {
  name = "types-and-programming-languages";
  buildInputs = [
    agda
  ];
}
