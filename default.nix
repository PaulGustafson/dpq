{ mkDerivation, base, containers, directory, easyrender, filepath
, haskeline, hpack, indents, mtl, nominal, parsec, pretty, process
, stdenv, transformers
}:
mkDerivation {
  pname = "dpq";
  version = "0.0.1";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base containers directory easyrender filepath haskeline indents mtl
    nominal parsec pretty process transformers
  ];
  libraryToolDepends = [ hpack ];
  executableHaskellDepends = [
    base containers directory easyrender filepath haskeline indents mtl
    nominal parsec pretty process transformers
  ];
  testHaskellDepends = [
    base containers directory easyrender filepath haskeline indents mtl
    nominal parsec pretty process transformers
  ];
  prePatch = "hpack";
  description = "Dependently typed Proto-Quipper (Proto-Quipper-D)";
  license = stdenv.lib.licenses.bsd3;
}
