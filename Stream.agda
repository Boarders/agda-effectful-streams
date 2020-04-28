module Stream where

open import Categories.Functor
open import Categories.Category.Instance.Sets
open import Level using (0ℓ; _⊔_) renaming (suc to sucℓ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc; _+_)

open import Categories.Category.Instance.Sets using (Sets)
open import Category.Monad using (RawMonad)
open import Category.Functor using (RawFunctor)
open import Data.Unit using (⊤; tt)

open ≡-Reasoning

data Stream
       (m : Set -> Set)
       (a : Set)  : ℕ -> Set₁ where
  stop : Stream m a zero
  step  : ∀{x}{n} -> a -> m x ->  (x  -> Stream m a n) -> Stream m a (suc n)


data Reader
       (m : Set -> Set)
       (a : Set)
       (b : Set) : ℕ -> Set₁ where
  emit : b -> Reader m a b zero
  read : ∀ {n} -> (a -> Reader m a b n) -> Reader m a b (suc n)

cons
  :  {n : ℕ} {a : Set}{m₀ : Set -> Set}
  -> (m : RawMonad m₀)
  -> a
  -> Stream m₀ a n
  -> Stream m₀ a (suc n)
cons m a str = step a (pure tt) \ _ -> str
  where
  open RawMonad m


append
  :  {n n' : ℕ} {a : Set}{m₀ : Set -> Set}
  -> (m : RawMonad m₀)
  -> Stream m₀ a n -> Stream m₀ a n' -> Stream m₀ a (n + n')
append {zero} m str1 str2  = str2
append {suc n} m (step a mx x[cont]) str2 
  = step a mx \ x -> append m (x[cont] x) str2



process
   : {n : ℕ} {a b : Set}{m₀ : Set -> Set}
  -> (m : RawMonad m₀)
  -> Stream m₀ a n
  -> Reader m₀ a b n 
  -> m₀ b
process m stop (emit b) = return b
  where
  open RawMonad m
process m (step a mx cont[x]) (read cont[a]) 
  = mx >>= (\ x -> process m (cont[x] x) (cont[a] a))
  where
  open RawMonad m
