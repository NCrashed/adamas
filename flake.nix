{
  description = "Adamas — research-level functional language (QTT + algebraic effects + Perceus)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      rust-overlay,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };

        # Версия — из rust-toolchain.toml, тот же файл читает CI через rustup.
        rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;

        rustPlatform = pkgs.makeRustPlatform {
          cargo = rustToolchain;
          rustc = rustToolchain;
        };
      in
      {
        packages.default = rustPlatform.buildRustPackage {
          pname = "adamas";
          version = "0.0.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;

          meta = with pkgs.lib; {
            description = "Adamas compiler toolchain";
            homepage = "https://github.com/NCrashed/adamas";
            license = with licenses; [
              mit
              asl20
            ];
            mainProgram = "adamas";
          };
        };

        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            rustToolchain
            pkgs.cargo-insta
            pkgs.cargo-mutants
          ];
        };

        # nixfmt-tree, а не голый nixfmt: последний на `nix fmt` без аргументов
        # читает пустой stdin и падает, а на директории ругается deprecation'ом.
        formatter = pkgs.nixfmt-tree;
      }
    );
}
