# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

{ stdenvNoCC
, fetchFromGitHub
, writeText
}:

stdenvNoCC.mkDerivation {
  pname = "mldsa-native-m55-an547";
  version = "main-2025-10-13";

  # Fetch platform files from pqmx (envs/m55-an547)
  src = fetchFromGitHub {
    owner = "bremoran";
    repo = "pqmx";
    rev = "3b4177cb76a614ed1887bcc2f90e571469d6fe2f";
    hash = "sha256-27ur5JYtZbwQ0fnrp/0Cj/R60TaZwouimFgOJGPjpMk=";
  };

  dontBuild = true;

  installPhase = ''
    mkdir -p $out/platform/m55-an547/src/platform/
    cp -r envs/m55-an547/src/platform/. $out/platform/m55-an547/src/platform/
    cp integration/*.c $out/platform/m55-an547/src/platform/
  '';

  setupHook = writeText "setup-hook.sh" ''
    export M55_AN547_PATH="$1/platform/m55-an547/src/platform/"
  '';

  meta = {
    description = "Platform files for the Cortex-M55 (AN547)";
    homepage = "https://github.com/slothy-optimizer/pqmx";
  };
}
