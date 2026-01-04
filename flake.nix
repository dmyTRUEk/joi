{
	inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

	outputs = { self, nixpkgs }:
	let
		system = "x86_64-linux";
		pkgs = import nixpkgs { inherit system; };
	in {
		packages.${system}.default = pkgs.rustPlatform.buildRustPackage {
			pname = "joi";
			version = "0.0.0";
			src = self;
			cargoLock.lockFile = ./Cargo.lock;
		};

		apps.${system}.default = {
			type = "app";
			program = "${self.packages.${system}.default}/bin/${self.packages.${system}.default.pname}";
		};
	};
}
