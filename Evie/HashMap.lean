import Lean.Data.HashMap

namespace Evie

def HashMap.modify [BEq α] [Hashable α] (a: α) (f: Option β -> β)(hm: Lean.HashMap α β): Lean.HashMap α β :=
  hm.insert a ∘ f ∘ hm.find? $ a

def HashMap.fromList [BEq α] [Hashable α]: List (α × β) -> Lean.HashMap α β
  | []           => Lean.HashMap.empty
  | (a, b) :: xs => Lean.HashMap.insert (HashMap.fromList xs) a b

def HashMap.keys [BEq α] [Hashable α]: Lean.HashMap α β -> List α :=
  List.map Prod.fst ∘ Lean.HashMap.toList

def HashMap.values [BEq α] [Hashable α]: Lean.HashMap α β -> List β :=
  List.map Prod.snd ∘ Lean.HashMap.toList
