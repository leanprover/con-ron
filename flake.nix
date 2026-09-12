{
  description = "con-ron: a Rust port of con-leche, proven to refine it via Aeneas";

  inputs = {
    # Aeneas pins the Charon commit it needs (see `charon-pin` upstream) and
    # Charon pins the Rust nightly it needs (`rust-toolchain`).  Everything
    # else follows from these two so that the Rust we write is compiled by
    # exactly the toolchain Charon understands.
    aeneas.url = "github:AeneasVerif/aeneas/505b6ca35217e7be5c96c3e2f8045edfbdf47291";
    nixpkgs.follows = "aeneas/charon/nixpkgs";
    flake-utils.follows = "aeneas/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, aeneas, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        charonPkgs = aeneas.inputs.charon.packages.${system};
        aeneasPkgs = aeneas.packages.${system};
      in {
        packages = {
          charon = charonPkgs.charon;
          aeneas = aeneasPkgs.aeneas;
          rustToolchain = charonPkgs.rustToolchain;
        };

        devShells.default = pkgs.mkShell {
          packages = [
            charonPkgs.rustToolchain   # rustc/cargo nightly pinned by Charon
            charonPkgs.charon          # `charon cargo --preset=aeneas`
            aeneasPkgs.aeneas          # `aeneas -backend lean`
            pkgs.jq
            pkgs.python3
          ];
          # Lean itself comes from the system `elan` (toolchains are per
          # project via `lean-toolchain`), so it is deliberately not here.
          shellHook = ''
            export CON_RON_ROOT="$PWD"
          '';
        };
      });
}
