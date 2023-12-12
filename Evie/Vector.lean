import Evie.Prelude

namespace Evie

inductive Vector (α: Type u): Nat -> Type u where
  | nil : Vector α 0
  | cons: α -> Vector α n -> Vector α (n + 1)

namespace Vector
open Evie.Prelude

def fromList (xs: List α): Vector α (xs.length) :=
  match xs with
    | [] => Vector.nil
    | x :: xs => Vector.cons x (fromList xs)

def get: Fin n -> Vector α n -> α
  | ⟨0, _⟩         , .cons x _  => x
  | ⟨Nat.succ i, h⟩, .cons _ xs => get ⟨i, Nat.le_of_succ_le_succ h⟩ xs

def map: (α -> β) -> Vector α n -> Vector β n
  | f, Vector.nil       => Vector.nil
  | f, Vector.cons a as => Vector.cons (f a) $ map f as

def toList: Vector α n -> List α
  | Vector.nil => []
  | Vector.cons a as => a :: toList as

def asString: Vector Char n -> String :=
  List.asString ∘ toList

def length: Vector α n -> Nat :=
  λ _ => n

def replicate: (n: Nat) -> α -> Vector α n
  | 0    , _ => Vector.nil
  | n + 1, a => Vector.cons a (replicate n a)

def enumFrom: Nat -> Vector α n -> Vector (Nat × α) n
  | _, Vector.nil       => Vector.nil
  | n, Vector.cons x xs => Vector.cons (n, x) $ enumFrom (n+1) xs

def enum: Vector α n -> Vector (Nat × α) n := enumFrom 0

def mapWithIdx (f: Nat -> α -> β): Vector α n -> Vector β n :=
  map (uncurry f) ∘ enum

def findPositionAux (f: α -> Bool) (c: Nat) (v: Vector α n): Option (Fin n) :=
  if h: c < n
    then
      if f $ v.get ⟨c, h⟩
        then .some ⟨c, h⟩
        else findPositionAux f (c + 1) v
    else none
termination_by _ => v.length - c

def findPosition (f: α -> Bool): Vector α n -> Option (Fin n) :=
  findPositionAux f 0

def updateAt (a: α): Fin n -> Vector α n -> Vector α n
  | ⟨0, _⟩, Vector.cons _ xs => Vector.cons a xs
  | ⟨k + 1, h⟩, Vector.cons x xs => Vector.cons x $ updateAt a ⟨k, Nat.le_of_succ_le_succ h⟩ xs
