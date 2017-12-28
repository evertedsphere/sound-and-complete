#!/bin/sh
NIX_GHC_VERSION="$(ghc --numeric-version)";     
export NIX_GHC_LIBDIR="$(dirname $(type -p ghc))/../lib/ghc-${NIX_GHC_VERSION}"; 

export cabal_helper_libexecdir=$(dirname $(which ghc))
