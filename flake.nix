{
  description = "Gaulois: general, composable program analyses in Rocq";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/c9fe7d12cd78d1adcd12dd15e24432dde5b155a0";

  outputs =
    { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];
      pkgsFor = system: import nixpkgs { inherit system; };
    in
    {
      devShells = nixpkgs.lib.genAttrs systems (system: {
        default = (import ./nix { pkgs = pkgsFor system; }).devShell;
      });
      formatter = nixpkgs.lib.genAttrs systems (system: (pkgsFor system).nixfmt);
    };
}
