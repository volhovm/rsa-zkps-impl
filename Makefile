all:
	NIXPKGS_ALLOW_INSECURE=1 nix-shell shell.nix --command "cargo bench --no-run"

test:
	NIXPKGS_ALLOW_INSECURE=1 nix-shell shell.nix --command "cargo test"

shell:
	NIXPKGS_ALLOW_INSECURE=1 nix-shell shell.nix
