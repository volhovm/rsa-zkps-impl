all:
	nix-shell -p pkgconfig gmp --command "cargo build"
