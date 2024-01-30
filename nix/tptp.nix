# NOTE: copied (with a few edits) from <https://github.com/NixOS/nixpkgs/blob/master/pkgs/applications/science/logic/z3/tptp.nix>

{ cmake, stdenv, z3 }:
let inherit (z3) src version;
in stdenv.mkDerivation {
  inherit src version;
  pname = "z3-tptp";
  sourceRoot = "${src.name}/examples/tptp";
  nativeBuildInputs = [ cmake ];
  buildInputs = [ z3 ];
  preConfigure = ''
    echo 'set(Z3_LIBRARIES "-lz3")' >> CMakeLists.new
    cat CMakeLists.txt | grep -E 'add_executable|project|link_libraries' >> CMakeLists.new
    mv CMakeLists.new CMakeLists.txt
  '';
  installPhase = ''
    mkdir -p "$out/bin"
    cp "z3_tptp5" "$out/bin/z3_tptp" # NOTE: single biggest change is the underscore in `z3_tptp`!
  '';
}
