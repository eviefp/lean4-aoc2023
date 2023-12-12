namespace Evie.Prelude

def curry: (α × β -> γ) -> α -> β -> γ
  | f, a, b => f (a, b)

def uncurry: (α -> β -> γ) -> (α × β) -> γ
  | f, (a, b) => f a b

def Option.maybe (f: α -> β) (b: β): (Option α) -> β
  | .some a => f a
  | .none   => b

def StateT.modify' [Monad m] (f : σ → σ) : StateT σ m Unit :=
  fun s => pure ((), f s)

def choice [Alternative f]: List (f α) -> f α :=
  List.foldl (λ acc cur => cur <|> acc) failure
