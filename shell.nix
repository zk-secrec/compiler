{ pkgs ? import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/refs/tags/21.05.tar.gz") {} }:

with pkgs; mkShell {
  buildInputs = [
    haskell.compiler.ghc8104
    stack
    haskell-language-server
    hlint
    ormolu
    nodePackages.npm
  ];
}
