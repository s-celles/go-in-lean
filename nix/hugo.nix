{ lib, stdenvNoCC, fetchurl, autoPatchelfHook, stdenv }:
let
  version = lib.strings.trim (builtins.readFile ../site/hugo-version);
  releases = {
    x86_64-linux = { platform = "linux-amd64"; sha256 = "416bcfbdf5f68469ec9644dbe507da50fc21b94b69a125b059d64ed2cb4d8c27"; };
    aarch64-linux = { platform = "linux-arm64"; sha256 = "dc070bfcc2803f068f21c6cb996a6782c8f9a2477be24bab574d51b6b280d241"; };
    x86_64-darwin = { platform = "darwin-universal"; sha256 = "23e59fcd6951dadc0ee7552c918970aa0c9b00659566f0fa591837e204e87d39"; };
    aarch64-darwin = { platform = "darwin-universal"; sha256 = "23e59fcd6951dadc0ee7552c918970aa0c9b00659566f0fa591837e204e87d39"; };
  };
  release = releases.${stdenvNoCC.hostPlatform.system};
in stdenvNoCC.mkDerivation {
  pname = "hugo-extended-pinned";
  inherit version;
  src = fetchurl {
    url = "https://github.com/gohugoio/hugo/releases/download/v${version}/hugo_extended_${version}_${release.platform}.tar.gz";
    inherit (release) sha256;
  };
  sourceRoot = ".";
  nativeBuildInputs = lib.optionals stdenvNoCC.hostPlatform.isLinux [ autoPatchelfHook ];
  buildInputs = lib.optionals stdenvNoCC.hostPlatform.isLinux [ stdenv.cc.cc.lib ];
  dontConfigure = true;
  dontBuild = true;
  installPhase = ''
    runHook preInstall
    install -Dm755 hugo "$out/bin/hugo"
    runHook postInstall
  '';
  meta = { description = "Pinned Hugo Extended for the go-in-lean website"; license = lib.licenses.asl20; platforms = builtins.attrNames releases; mainProgram = "hugo"; };
}
