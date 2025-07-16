{
  description = "Probability and Statistics - Cheat Sheet";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";

    # Systems, gets a list of systems, allows easy overriding
    systems.url = "github:nix-systems/default";
  };

  outputs = inputs: let
    eachSystem = inputs.nixpkgs.lib.genAttrs (import inputs.systems);
    pkgsFor = inputs.nixpkgs.legacyPackages;
  in {
    devShells = eachSystem (system: {
      default = pkgsFor.${system}.callPackage ./shell.nix {};
    });

    # set up formatter for each system
    formatter = eachSystem (
      system: pkgsFor.${system}.alejandra
    );
  };
}
