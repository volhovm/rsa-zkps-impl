all:
	nix-shell -p gmp gnum4 --command "cargo build"
