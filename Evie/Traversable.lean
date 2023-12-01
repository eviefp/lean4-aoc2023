import Evie.Monoid
open Evie.Monoid

namespace Evie
namespace Foldable

structure Foldable where
  Container : Type -> Type
  foldMap : (M: Monoid) -> (α -> M.Carrier) -> Container α -> M.Carrier

-- List
namespace List

def foldMap (M: Monoid) (f: α -> M.Carrier) (xs: List α): M.Carrier :=
  List.foldl M.op M.unit ∘ List.map f $ xs

def Instance: Foldable :=
  { Container := List
  , foldMap := foldMap
  }

end List

-- Option
namespace Option

def foldMap (M: Monoid) (f: α -> M.Carrier) (o: Option α): M.Carrier :=
  match o with
  | some s => f s
  | none => M.unit

def Instance: Foldable :=
  { Container := Option
  , foldMap := foldMap
  }

end Option

end Foldable

namespace Traversable

def liftA2
  [S: Seq f]
  [F: Functor f]
  (fn: α -> β -> γ)
  (xs: f α)
  (ys: f β)
  : f γ :=
    S.seq (F.map fn xs) (fun _ => ys)

structure Traversable where
  foldable : Foldable.Foldable
  traverse
    :  [Applicative f]
    -> (α -> f β)
    -> foldable.Container α
    -> f (foldable.Container β)

def Traversable.sequenceA
  [Applicative f]
  (T: Traversable)
  :  T.foldable.Container (f α)
  -> f (T.foldable.Container α) := T.traverse id

-- List
namespace List

def traverse
  [A: Applicative f]
  (fn: α -> f β)
  (xs: List α)
  : f (List β) :=
    let go := fun y ys =>
        liftA2 List.cons (fn y) ys
    List.foldr go (pure []) xs

def Instance : Traversable :=
  { foldable := Evie.Foldable.List.Instance
  , traverse := traverse
  }

end List

-- Option
namespace Option

def traverse
  [A: Applicative f]
  (fn: α -> f β)
  (xs: Option α)
  : f (Option β) :=
    match xs with
    | none => A.pure none
    | some x => some <$> fn x

def Instance : Traversable :=
  { foldable := Evie.Foldable.Option.Instance
  , traverse := traverse
  }

end Option
