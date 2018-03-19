{-# LANGUAGE NoImplicitPrelude, GADTs, TypeFamilies, DataKinds, PolyKinds #-}

module Peano where

-- Define heterogenous propositional equality
data Eq :: a -> b -> * where
    Refl :: Eq x x

-- Define Peano numbers at the type level: note that here Nat is a kind, Z and S n are types.
data Nat = Z | S Nat

-- Facilitate type-level operations at the term level using a singleton type.
-- This uses a GADT to associate types of kind Nat with the respective construtors of Nat'.
data Nat' s where
    Z' :: Nat' Z
    S' :: Nat' n -> Nat' (S n)

-- Type-level addition.
type family Plus (n :: Nat) (m :: Nat) :: Nat where
    Plus x Z = x
    Plus x (S y) = S (Plus x y)

-- Equality is preserved under function application.
under :: Eq a b -> Eq (f a) (f b)
under Refl = Refl

-- Simple inductive proof that the previously-defined type-level addition is associative.
plusAssociates :: Nat' m -> Nat' n -> Nat' p -> Eq (Plus (Plus m n) p) (Plus m (Plus n p))
plusAssociates _ _ Z' = Refl
plusAssociates m n (S' p) = under (plusAssociates m n p)
