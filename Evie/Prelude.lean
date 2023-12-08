namespace Evie.Prelude

def Option.maybe (f: α -> β) (b: β): (Option α) -> β
  | .some a => f a
  | .none   => b

def StateT.modify' [Monad m] (f : σ → σ) : StateT σ m Unit :=
  fun s => pure ((), f s)

def choice [Alternative f]: List (f α) -> f α :=
  List.foldl (λ acc cur => cur <|> acc) failure
