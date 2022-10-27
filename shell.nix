#with import (builtins.fetchTarball {
#    name = "nixos-22.05";
#    url = "https://github.com/nixos/nixpkgs/archive/ce6aa13369b667ac2542593170993504932eb836.tar.gz";
#    sha256 = "0d643wp3l77hv2pmg2fi7vyxn4rwy0iyr8djcw1h5x72315ck9ik";
#}) {};
with import (builtins.fetchTarball {
    name = "nixos-22.11-pre";
    url = "https://github.com/nixos/nixpkgs/archive/104e8082de1b20f9d0e1f05b1028795ed0e0e4bc.tar.gz";
    sha256 = "1y7j4bgk6wcipy9vmfmdgy8pv1wp3mq76sdjc4yib7xdn0bvgxvh";
}) {};
(pkgs.mkShell rec {
    buildInputs = with pkgs; [
      llvmPackages_latest.llvm
      llvmPackages_latest.bintools
      zlib.out
      rustup
      xorriso
     # grub2
     #  qemu
      m4
      llvmPackages_latest.lld
      python3
      gmp
      gnum4
    ];
    RUSTC_VERSION = pkgs.lib.readFile ./rust-toolchain;
    # https://github.com/rust-lang/rust-bindgen#environment-variables
    LIBCLANG_PATH= pkgs.lib.makeLibraryPath [ pkgs.llvmPackages_latest.libclang.lib ];
    HISTFILE=toString ./.history;
    shellHook = ''
      export PATH=$PATH:~/.cargo/bin
      export PATH=$PATH:~/.rustup/toolchains/$RUSTC_VERSION-x86_64-unknown-linux-gnu/bin/
      '';
    # Add libvmi precompiled library to rustc search path
#    RUSTFLAGS = (builtins.map (a: ''-L ${a}/lib'') [
#      pkgs.libvmi
#    ]);
#    # Add libvmi, glibc, clang, glib headers to bindgen search path
#    BINDGEN_EXTRA_CLANG_ARGS =
#    # Includes with normal include path
#    (builtins.map (a: ''-I"${a}/include"'') [
#      pkgs.libvmi
#      pkgs.glibc.dev
#    ])
#    # Includes with special directory paths
#    ++ [
#      ''-I"${pkgs.llvmPackages_latest.libclang.lib}/lib/clang/${pkgs.llvmPackages_latest.libclang.version}/include"''
#      ''-I"${pkgs.glib.dev}/include/glib-2.0"''
#      ''-I${pkgs.glib.out}/lib/glib-2.0/include/''
#    ];
})
