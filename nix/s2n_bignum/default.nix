# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "a279d744250802c6d60fcb77c3ba337e5a869495";
  src = fetchFromGitHub {
    owner = "mkannwischer";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-dtXc7OV0Pl60ZJUTKMmZNwlNsXUQWcY1eb2VpKbgxEQ=";
  };
  setupHook = writeText "setup-hook.sh" ''
    export S2N_BIGNUM_DIR="$1"
  '';
  patches = [ ];
  dontBuild = true;
  installPhase = ''
    mkdir -p $out
    cp -a . $out/
  '';
}
