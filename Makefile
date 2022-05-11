all:
	NIXPKGS_ALLOW_INSECURE=1 nix-shell shell.nix --command "cargo bench --no-run"
