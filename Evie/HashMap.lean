import Lean.Data.HashMap

namespace Evie.HashMap

def modify [BEq α] [Hashable α] (a: α) (f: Option β -> β)(hm: Lean.HashMap α β): Lean.HashMap α β :=
  hm.insert a ∘ f ∘ hm.find? $ a