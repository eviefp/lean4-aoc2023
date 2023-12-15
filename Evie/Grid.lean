import Evie.List
import Evie.Prelude
import Evie.Vector

namespace Evie
open Evie.Prelude

structure Grid (x: Nat) (y: Nat) (α: Type) where
  data: Vector (Vector α x) y

instance [S: ToString α] : ToString (Grid x y α) where
  toString :=
    String.intercalate "\n"
      ∘ Vector.toList
      ∘ Vector.map (String.join ∘ List.map S.toString ∘ Vector.toList)
      ∘ Grid.data

def Grid.replicate (x: Nat) (y: Nat) (a: α): Grid x y α :=
  Grid.mk
    ∘ Vector.replicate y
    ∘ Vector.replicate x
    $ a



def Grid.mapWithPosition (f: (Nat × Nat) -> α -> β): Grid x y α -> Grid x y β :=
  Grid.mk
    ∘ Vector.mapWithIdx (λ y' line => line.mapWithIdx (λ x' a => f ⟨x', y'⟩ a))
    ∘ Grid.data


def Grid.mapMWithPosition
  [Monad m]
  (f: (Nat × Nat) -> α -> m β)
  (grid: Grid x y α):
  m (Grid x y β) :=
  Grid.mk <$>
    Vector.mapMWithIdx
      (λ y' line => line.mapMWithIdx (λ x' a => f ⟨x', y'⟩ a))
      grid.data

def Grid.foldWithIdx (f: (Nat × Nat) -> β -> α -> β) (init: β): Grid x y α -> β :=
  Vector.foldWithIdx
    (λ y' by' line => line.foldWithIdx (λ x' bx' a => f ⟨x', y'⟩ bx' a) by' )
    init
    ∘ Grid.data

def Grid.foldlWithIdx (f: (Nat × Nat) -> β -> α -> β) (init: β): Grid x y α -> β :=
  Grid.foldWithIdx f init

def Grid.foldrWithIdx (f: (Nat × Nat) -> β -> α -> β) (init: β): Grid x y α -> β :=
  Vector.foldrWithIdx
    (λ y' by' line => line.foldrWithIdx (λ x' bx' a => f ⟨x', y'⟩ bx' a) by' )
    init
    ∘ Grid.data

def Grid.fromList (x y: Nat) (default: α) (l: List (List α)): Grid x y α :=
  Grid.mapWithPosition
    (λ (x, y) a =>
      let result := List.get? l y >>= (λ line => List.get? line x)
      Option.maybe id a result
    )
    $ Grid.replicate x y default

structure Grid.Position (x: Nat) (y: Nat) where
  x: Fin x
  y: Fin y
deriving Hashable, BEq

instance: ToString (Grid.Position x y) where
  toString p := s!"⟨{p.x.val}, {p.y.val}⟩"

def Grid.Position.mkPosition (x y: Nat) (x' y': Nat): Option (Position x y) :=
    if hy: y' < y
    then if hx: x' < x
      then some
        { x := ⟨x', hx⟩
        , y := ⟨y', hy⟩
        }
      else none
    else none

def Grid.Position.up (pos: Grid.Position x₁ y₁): Option (Grid.Position x₁ y₁) :=
  if h: pos.y.val ≠ 0
    then
      some
        { x := pos.x
        , y := ⟨Nat.pred pos.y.val, trans (Nat.pred_lt h) pos.y.isLt⟩
        }
    else none

def Grid.Position.down (pos: Grid.Position x₁ y₁): Option (Grid.Position x₁ y₁) :=
  if h: pos.y.val + 1 < y₁
    then
      some
        { x := pos.x
        , y := ⟨pos.y.val + 1, h⟩
        }
    else none

def Grid.Position.left (pos: Grid.Position x₁ y₁): Option (Grid.Position x₁ y₁) :=
  if h: pos.x.val ≠ 0
    then
      some
        { x := ⟨Nat.pred pos.x.val, trans (Nat.pred_lt h) pos.x.isLt⟩
        , y := pos.y
        }
    else none

def Grid.Position.right (pos: Grid.Position x₁ y₁): Option (Grid.Position x₁ y₁) :=
  if h: pos.x.val + 1 < x₁
    then
      some
        { x := ⟨pos.x.val + 1, h⟩
        , y := pos.y
        }
    else none

def Grid.Position.neighbors (pos: Grid.Position m n): List (Grid.Position m n) :=
  List.catMaybes
    [ pos.up
    , pos.down
    , pos.left
    , pos.right
    ]


def Grid.get (pos: Position x y): Grid x y α -> α :=
  Vector.get pos.x ∘ Vector.get pos.y ∘ Grid.data

def Grid.updateAt (pos: Position x y) (f: α -> α): Grid x y α -> Grid x y α :=
  Grid.mk
    ∘ Vector.updateAt pos.y (Vector.updateAt pos.x f)
    ∘ Grid.data
