namespace Evie

namespace Monoid

structure Monoid where
  Carrier : Type
  unit : Carrier
  op : Carrier -> Carrier -> Carrier

def Monoid.fold (M: Monoid) (xs: List M.Carrier): M.Carrier :=
  List.foldl M.op M.unit xs

def Monoid.foldMapM
  [Monad m]
  (M: Monoid)
  (f: α -> m M.Carrier)
  (xs: List α)
  : m M.Carrier :=
  xs.foldlM
    (fun acc a => do
      let current <- f a
      pure $ M.op acc current
    ) M.unit

def Monoid.foldMap (M: Monoid) (f: α -> M.Carrier) (xs: List α): M.Carrier :=
  M.fold $ xs.map f

-- First
namespace First

def compose (first : Option α) (second: Option α): Option α :=
      match first, second with
      | .some _, _ => first
      | _, _ => second

def Instance {α : Type}: Monoid :=
  { Carrier := Option α
  , unit := none
  , op := compose
  }

end First

-- Last
namespace Last

def compose (first : Option α) (second: Option α): Option α :=
  match first, second with
  | _, .none => first
  | _, _ => second

def Instance {α : Type}: Monoid :=
  { Carrier := Option α
  , unit := none
  , op := compose
  }

end Last

namespace Nat

namespace Sum

def Instance:  Monoid :=
  { Carrier := Nat
  , unit := 0
  , op := Nat.add
  }

end Sum

namespace Product

def Instance:  Monoid :=
  { Carrier := Nat
  , unit := 1
  , op := Nat.mul
  }

end Product

namespace Min

def compose: Option Nat -> Option Nat -> Option Nat
  | some m, some n => some $ Nat.min m n
  | o1    , o2     => o1 <|> o2

-- Don't have Nat.MaxNumber so we have to make do with Option
def Instance: Monoid :=
  { Carrier := Option Nat
  , unit := none
  , op := compose
  }

end Min

end Nat
