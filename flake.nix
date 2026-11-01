{
  description = "go-in-lean: finding Go stdlib bugs with Lean 4 (dev shell)";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          # Lean itself is installed by elan from `lean-toolchain` (pinned
          # v4.35.0) because nixpkgs lags behind Lean releases. Go is pinned
          # to the 1.25 series; `scripts/check.sh` prints a warning if the
          # patch version differs from go/.go-version.
          packages = [ pkgs.elan pkgs.go_1_25 pkgs.python3 pkgs.git ];
          shellHook = ''
            export ELAN_HOME="$PWD/.lake/elan"
            export PATH="$ELAN_HOME/bin:$PATH"
            echo "go-in-lean dev shell: $(go version); run 'elan toolchain install $(cat lean-toolchain)' once, then scripts/check.sh"
          '';
        };
      });
    };
}
