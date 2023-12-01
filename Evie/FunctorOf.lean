namespace Evie

namespace FunctorOf

structure FunctorOf where
  SourceRelationship : Type -> Type -> Type
  TargetRelationship : Type -> Type -> Type
  Functor : Type -> Type
  fmap
    :  SourceRelationship α β
    -> TargetRelationship (Functor α) (Functor β)

def Fn (α : Type) (β : Type) : Type := α -> β

def Compose (f: Type -> Type) (g: Type -> Type) (x: Type) := f (g x)

namespace Functor

def Instance [F: Functor f]: FunctorOf :=
  { SourceRelationship := Fn
  , TargetRelationship := Fn
  , Functor := f
  , fmap := F.map
  }

end Functor

namespace Functor2

def Instance [F1: Functor f] [F2: Functor g]: FunctorOf :=
  { SourceRelationship := Fn
  , TargetRelationship := Fn
  , Functor := Compose f g
  , fmap := F1.map ∘ F2.map
  }

end Functor2

namespace Functor3

def Instance
  [F1: Functor f]
  [F2: Functor g]
  [F3: Functor h]
  : FunctorOf :=
    { SourceRelationship := Fn
    , TargetRelationship := Fn
    , Functor := Compose f (Compose g h)
    , fmap := F1.map ∘ F2.map ∘ F3.map
    }

end Functor3

def map1
  [Functor f]
  :  (α -> β)
  -> f α
  -> f β
  := Functor.Instance.fmap

def map2
  [Functor f]
  [Functor g]
  :  (α -> β)
  -> f (g α)
  -> f (g β)
  := Functor2.Instance.fmap

def map3
  [Functor f]
  [Functor g]
  [Functor h]
  :  (α -> β)
  -> f (g (h α))
  -> f (g (h β))
  := Functor3.Instance.fmap
