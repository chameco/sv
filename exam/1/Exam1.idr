module Exam1
  
-- Here are the proofs requested in exam 1.
-- All properties are expressed within the Idris type system, and proven by inhabiting those types.
-- The following correspondences between logical formulae and types are used (by the Curry-Howard correspondence):
--   universal quantification is the dependent product type: forall x. P x is ((x : Object) -> P x)
--   existential quantification is the dependent sum type: exists x. P x is (x : Object ** P x)
--   implication is the non-dependent function type (since implication is just a special case of universal quantification): p -> q is p -> q
--   conjunction is the non-dependent product type, or the pair: p AND q is (p, q)
--   disjunction is the sum type: p OR q is (p | q) (which must be defined as a datatype, e.g. Either in Haskell)

-- Turn on the Idris totality checker.
-- Without this our programs are not necessarily proofs, since it is possible that they will not terminate.
%default total
  
-- Disjunction and conjunction as sum and product types. These definitions are just for convenience.
data Or a b = Left a | Right b
data And a b = UnAnd a b
  
-- I use an uninhabited type as the domain here, but this is arbitrary.
data Object : Type where

-- Define the goal, which yields the goal from the exam book given two predicates P and Q.
-- The goal below appears much longer than the one in the exam due to the need to express
-- p iff q as (p -> q) and (q -> p), since as far as I know there is not a more concise way
-- to express iff in the Curry-Howard correspondence .
q1goal : (Object -> Type) -> (Object -> Type) -> Type
q1goal P Q = (And ((x : Object ** (Or (P x) (Q x))) -> (Or (x : Object ** (P x)) (x : Object ** (Q x))))
                  ((Or (x : Object ** (P x)) (x : Object ** (Q x))) -> (x : Object ** (Or (P x) (Q x)))))

-- Proof by cases for the "forwards" case, i.e. (exists x . P x | Q x) -> (exists x . P x) | (exists x . Q x)
q1proof1lemma1 : (p : Object -> Type) -> (q : Object -> Type) -> (x : Object ** Or (p x) (q x)) -> Or (x : Object ** p x) (x : Object ** q x)
q1proof1lemma1 _ _ (x ** Left px) = Left (x ** px)
q1proof1lemma1 _ _ (x ** Right qx) = Right (x ** qx)

-- Proof by cases for the "backwards" case, i.e. (exists x . P x) | (exists x . Q x) -> (exists x . P x | Q x)
q1proof1lemma2 : (p : Object -> Type) -> (q : Object -> Type) -> Or (x : Object ** p x) (x : Object ** q x) -> (x : Object ** Or (p x) (q x))
q1proof1lemma2 _ _ (Left (x ** px)) = (x ** Left px)
q1proof1lemma2 _ _ (Right (x ** qx)) = (x ** Right qx)

-- The complete proof. Since we have proven both directions of the iff, we simply introduce their conjunction.
q1proof1 : (p : Object -> Type) -> (q : Object -> Type) -> q1goal p q
q1proof1 p q = UnAnd (q1proof1lemma1 p q) (q1proof1lemma2 p q)

-- A definition for forward quantifier distribution over disjunction. Notice that this definition is identical to q1proof1lemma1.
quantDistOrFor : {p : Object -> Type} -> {q : Object -> Type} -> (x : Object ** Or (p x) (q x)) -> Or (x : Object ** p x) (x : Object ** q x)
quantDistOrFor (x ** Left px) = Left (x ** px)
quantDistOrFor (x ** Right qx) = Right (x ** qx)

-- A definition for backward quantifier distribution over disjunction. Notice that this definition is identical to q1proof1lemma2.
quantDistOrRev : {p : Object -> Type} -> {q : Object -> Type} -> Or (x : Object ** p x) (x : Object ** q x) -> (x : Object ** Or (p x) (q x))
quantDistOrRev (Left (x ** px)) = (x ** Left px)
quantDistOrRev (Right (x ** qx)) = (x ** Right qx)

-- Bidirectional quantifier distribution over disjunction using the above two definitions. Notice that this is identical to q1proof1.
quantDistOr : {P : Object -> Type} -> {Q : Object -> Type} -> (And ((x : Object ** (Or (P x) (Q x))) -> (Or (x : Object ** (P x)) (x : Object ** (Q x))))
                                                                   ((Or (x : Object ** (P x)) (x : Object ** (Q x))) -> (x : Object ** (Or (P x) (Q x)))))
quantDistOr = UnAnd quantDistOrFor quantDistOrRev

-- Finally, the second proof (using quantifier distribution).
q1proof2 : q1goal p q
q1proof2 = quantDistOr

-- Notice that here, unlike in the previous problem, there are assumptions.
-- We cannot simply assert these in Idris. In order to prove P x given some assumption Q x, we instead
-- prove Q x -> P x.
q2goal : (Object -> Type) -> (Object -> Type) -> (Object -> Object -> Type) -> Type
q2goal P Q R = (x : Object ** P x) -> (x : Object ** Q x) -> ((x : Object) -> P x -> (y : Object) -> Q y -> R x y) -> (x : Object ** (y : Object ** R x y))

-- Here, the proof is trivial: it is known that there exists some x that satisfies P x and some y that satisfies Q y,
-- so therefore we can simply apply the third assumption to x, px, y, and qy to yield R x y.
-- We can then construct the existential quantifier (as the sigma type), as we have x, y, and R x y.
q2proof : q2goal p q r
q2proof (x ** px) (y ** qy) a3 = (x ** (y ** a3 x px y qy))
