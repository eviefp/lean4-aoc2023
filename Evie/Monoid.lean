namespace Evie

namespace Monoid

structure Monoid where
  Carrier : Type
  unit : Carrier
  op : Carrier -> Carrier -> Carrier

def Monoid.fold (M: Monoid) (xs: List M.Carrier): M.Carrier :=
  List.foldl M.op M.unit xs

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
