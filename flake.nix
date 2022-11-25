{
  inputs = {
    nixpkgs = {
      type = "github";
      owner = "NixOS";
      repo = "nixpkgs";
      ref = "nixos-unstable";
    };
  };

  outputs = inputs:
    let pkgs = import inputs.nixpkgs { system = "x86_64-linux"; };
    in {
      devShell.x86_64-linux = pkgs.mkShell {
        buildInputs = with pkgs;
          [ (agda.withPackages (pkgs: with pkgs; [ standard-library ])) ];
      };
    };
}
