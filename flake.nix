{
  description = "nanodatg — a proof-carrying Lean checker in Rust";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # The Rust toolchain. We build a plain kernel with no external crates
        # (except a vetted bignum crate later — see kernel/README.md), so the
        # stock nixpkgs toolchain is all we need.
        rustToolchain = with pkgs; [
          cargo
          rustc
          rustfmt
          clippy
          rust-analyzer
        ];
      in
      {
        devShells.default = pkgs.mkShell {
          # mkShell's stdenv already provides a C compiler (cc) and linker (ld),
          # which cargo needs for the final link step.
          packages = rustToolchain ++ (with pkgs; [
            git
          ]);

          # Point rust-analyzer / tooling at the standard library source.
          RUST_SRC_PATH = "${pkgs.rustPlatform.rustLibSrc}";

          shellHook = ''
            echo "nanodatg dev shell — $(cargo --version)"
          '';
        };
      });
}
