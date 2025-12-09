{
  description = "Ice Nine - Cryptographic protocol with formal verification";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # Aeneas: Rust-to-Lean verification toolchain
    aeneas = {
      url = "github:AeneasVerif/aeneas";
      # Don't follow nixpkgs - Aeneas has specific OCaml/Coq version requirements
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      rust-overlay,
      aeneas,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [
            "rust-src"
            "rust-analyzer"
            "clippy"
            "rustfmt"
          ];
        };

      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Rust toolchain
            rustToolchain
            cargo-watch
            cargo-edit

            # Build tools
            pkg-config
            openssl

            # Task runner
            just

            # POSIX tools
            coreutils
            findutils
            gawk
            gnused

            # Lean 4 for formal verification
            lean4
            elan
            aeneas.packages.${system}.aeneas

            # Development tools
            git
            jq
            ripgrep

            # Deployment
            rclone
            rsync
          ];

          shellHook = ''
            echo "Ice Nine"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "Platform: ${system}"
            echo "Rust:     $(rustc --version)"
            echo "Lean:     $(lean --version 2>/dev/null || echo 'available')"
            echo "Elan:     $(elan --version 2>/dev/null || echo 'available')"
            echo "Aeneas:   $(aeneas --version 2>/dev/null || echo 'available')"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo ""
            echo "Commands:"
            echo "  just --list      Show all tasks"
            echo "  just build       Build Lean + Rust"
            echo "  just deploy      Sync & build on server"
            echo "  just ssh         SSH into server dev env"
            echo ""

            export RUST_BACKTRACE=1
            export MACOSX_DEPLOYMENT_TARGET=11.0
          '';
        };

        packages.default = pkgs.rustPlatform.buildRustPackage {
          pname = "ice-nine";
          version = "0.1.0";

          src = ./.;

          cargoLock = {
            lockFile = ./Cargo.lock;
          };

          nativeBuildInputs = with pkgs; [
            rustToolchain
            pkg-config
          ];

          buildInputs = with pkgs; [
            openssl
          ] ++ lib.optionals stdenv.isDarwin [
            libiconv
          ];

          meta = with pkgs.lib; {
            description = "Cryptographic protocol implementation with formal verification in Lean";
            license = licenses.mit;
            maintainers = [ ];
          };
        };
      }
    );
}
