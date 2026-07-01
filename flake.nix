{
  description = "AProVE";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachSystem [ flake-utils.lib.system.x86_64-linux ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        lib = pkgs.lib;

        jdk = pkgs.jdk25;
      in {
        packages.default = pkgs.stdenv.mkDerivation {
          name = "aprove";

          src = lib.fileset.toSource {
            root = ./.;
            fileset = lib.fileset.unions [
              ./build-aprove.xml
              ./src
              ./lib
              ./res-classes
              # ./.git ?
            ];
          };

          nativeBuildInputs = [ pkgs.ant jdk ];

          buildPhase = ''
            ant -f build-aprove.xml dist
          '';

          installPhase = ''
            mkdir -p $out/{bin,lib}
            cp dist/lib/aprove.jar $out/lib/.
            cat > $out/bin/aprove <<EOF
            #!${pkgs.runtimeShell}
            exec ${pkgs.jdk25}/bin/java -jar $out/lib/aprove.jar "\$@"
            EOF
            chmod +x $out/bin/aprove
          '';
        };

        apps.default = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/aprove";
        };

        devShells.default = pkgs.mkShell {
          packages = [ jdk pkgs.ant ];
        };
      });
}
