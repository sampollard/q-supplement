Module Type ConfigType.
  Parameter S : Set.
  Parameter E : Type.
  Inductive Config :=
  | U : Config
  | P : Config -> Config -> Config
  | N : S -> Config -> Config.
End ConfigType.

Module DefaultConfig <: ConfigType.
  Axiom S : Set.
  Axiom  E : Type.
  Inductive Config :=
  | U : Config
  | P : Config -> Config -> Config
  | N : S -> Config -> Config.
End DefaultConfig.


