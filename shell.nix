let 
  rien = import /home/frob/code/rien/rien.nix {
    packageName = "sound-and-complete";
    packagePath = ./.;

    # Instead of using <nixpkgs>, use a lock-file to stick to
    # a particular `nixpkgs` commit.
    nixpkgsLock = ./nixpkgs.json;

    ghcVersion = "ghc822";

    overrides = rec {
      # I don't want to use Brittany as a library!
      skipHaddock = justStaticExecutables;
      justStaticExecutables = [ 
        "brittany" 
        "hpack"
        "ghcid"
        "hlint"
      ];
    };
  };

in
  rien.shell {
    # Generate Hoogle documentation?
    wantHoogle = true;

    # Haskell dependencies
    deps = hsPkgs: with hsPkgs; [
      brittany
      hpack
      ghcid
      hlint
      adjunctions
      exceptions
      hashable
      hspec
      lens
      mtl
      prettyprinter
      prettyprinter-ansi-terminal
      profunctors
      safe
      text
      uniplate
      unordered-containers
    ];

    # Optionally, also add sets of related packages that are
    # commonly used together.
    depSets = hsPkgs: with (rien.package-sets hsPkgs); [
      development-servers
    ];

    # Native dependencies
    nativeDeps = pkgs: with pkgs; [ ];
  }
