{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    (pkgs.haskellPackages.ghcWithPackages (hpkgs: with hpkgs; [
      stack
      cabal-install
      haskell-language-server
    ]))
  ];
  shellHook = ''
    ghc --version
  '';
}
