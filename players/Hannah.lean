inductive myList (α : Type) where
  | nil
  | cons : α → myList α → myList α
  deriving Repr

notation:65 x:65 "::" l:66 => myList.cons x l
notation:10 "[" l "]" => l::myList.nil

inductive Maybe (α : Type) where
  | Nothing : Maybe α
  | Just : α → Maybe α
  deriving Repr
-- LEVEL 1: Recognizing


open myList-- Easier to write myList α things
open Nat
open Maybe

variable {α β γ : Type}

#check nil -- With open command
#check myList.nil -- Without "open myList α" command
#check cons 0 nil


-- LEVEL 2: Defining operations

def fmap : (α → β) → myList α → myList β
  | _, nil => nil
  | p, n::l => (p n)::(fmap p l)

def length : myList α → Nat
  | nil => 0
  | _::l => succ (length l)

def elem : Nat → myList Nat → Bool
  | _, nil => false
  | n, m::l => n == m || elem n l

def sum : myList Nat → Nat
  | nil => 0
  | n::l => n + (sum l)

def product : myList Nat → Nat
  | nil => 1
  | n::l => n * (product l)

-- Same as (++)
def concat : myList α → myList α → myList α
  | nil, list => list
  | n::l, list => n::(concat l list)
infixl:65   " ++ " => concat

-- Add an nat to the end
def append : α → myList α → myList α
  | n, nil => cons n nil
  | n, m::l => m::(append n l)

-- Define append in function of concat

def append_cat : α → myList α → myList α
  | n, list => list ++ (n::nil)

-- esreveR...
def reverse : myList α → myList α
  | nil => nil
  | n::l => append n (reverse l)

def rev : myList α → myList α
  | nil => nil
  | n::l => (rev l) ++ (n::nil)

def revcat : myList α → myList α → myList α
  | nil, ys => ys
  | x::xs, ys => revcat xs (x::ys)

def min₂ : Nat → Nat → Nat
  | n+1, m+1 => (min n m) + 1
  | _, _ => 0

def max₂ : Nat → Nat → Nat
  | 0, m => m
  | n, 0 => n
  | n+1, m+1 => (max n m) + 1

def filter : (α → Bool) → myList α → myList α
  | _, nil => nil
  | p, n::l => if p n then n::(filter p l) else filter p l

mutual
def even : Nat → Bool
  | 0 => true
  | succ n => odd n

def odd : Nat → Bool
  | 0 => false
  | succ n => even n
end

def Zero : Nat → Bool
  | 0 => true
  | _ => false

def All : (α → Bool) → myList α → Bool
  | _, nil => true
  | p, n::l => p n && All p l

def Any : (α → Bool) → myList α → Bool
  | _, nil => false
  | p, n::l => p n || Any p l

def doubleList : myList Nat → myList Nat
  := fun l => fmap (· * 2) l

def addNat : Nat → myList Nat → myList Nat
  := fun n => fun l => fmap (· + n) l

def multNat : Nat → myList Nat → myList Nat
  := fun n => fun l => fmap (· * n) l

def expNat : Nat → myList Nat → myList Nat
  := fun n => fun l => fmap (· ^ n) l

def enumTo : Nat → myList Nat
  | n+1 => append (n+1) (enumTo n)
  | _ => [0]

def replicate : Nat → α → myList α
  | 0, _ => nil
  | succ n, m => m::(replicate n m)

def take : Nat → myList α → myList α
  | n+1, m::l => m::(take n l)
  | _, _ => nil

def takeWhile : (α → Bool) → myList α → myList α
  | _, nil => nil
  | p, n::l => if p n then n::(takeWhile p l) else nil

def drop : Nat → myList α → myList α
  | n+1, _::l => drop n l
  | _, l => l

def dropWhile : (α → Bool) → myList α → myList α
  | _, nil => nil
  | p, n::l => if p n then dropWhile p l else n::l

def elemIndices : Nat → myList Nat → myList Nat
  | n, m::l => if n == m then 0::(addNat 1 (elemIndices n l)) else (addNat 1 (elemIndices n l))
  | _, nil => nil

def pw : (α → β → γ) → myList α → myList β → myList γ
  | o, n::l, m::l' => (o n m)::(pw o l l')
  | _, _, _ => nil

def pwAdd : myList Nat → myList Nat → myList Nat
  := fun l => fun r => pw (· + ·) l r

def pwMult : myList Nat → myList Nat → myList Nat
  := fun l => fun r => pw (· * ·) l r

def isSorted : myList Nat → Bool
  | n::(m::l) => n ≤ m && isSorted (m::l)
  | _ => true

def stripMaybe : Maybe Nat → Nat
  | Just n => n
  | Nothing => 0

def minimum : myList Nat → Maybe Nat
  | [n] => Just n
  | n::l => Just (min₂ n (stripMaybe (minimum l)))
  | _ => Nothing

def maximum : myList Nat → Nat
  | nil => 0
  | n::l => max₂ n (maximum l)

def isPrefixOf : myList Nat → myList Nat → Bool
  | nil, _ => true
  | n::ns, m::ms => n == m && isPrefixOf ns ms
  | _, _ => false

def mix : myList α → myList α → myList α
  | n::ns, m::ms => n::(m::(mix ns ms))
  | _, _ => nil

def interspace : α → myList α → myList α
  | _, [m] => [m]
  | n, m::l => m::(n::(interspace n l))
  | _, nil => nil

-- Assume ordered lists
-- First element greater than n
def upper_bound : Nat → myList Nat → Nat
  | _, nil => 0
  | n, m::l => if m > n then m else upper_bound n l

-- Assume ordered lists
-- First element not less than n
def lower_bound : Nat → myList Nat → Nat
  | _, nil => 0
  | n, m::l => if m ≥ n then m else lower_bound n l

-- LEVEL 3: Theorems

theorem concat_nil (l : myList α) :
  l ++ (nil : myList α) = l :=
by
  induction l with
  | nil => rw [concat]
  | cons x xs h => rw [concat, h]

theorem concat_append (x : α) (xs ys : myList α) :
  ys ++ (append x xs) = append x (ys ++ xs) :=
by
  induction ys with
  | nil => rw [concat, concat]
  | cons y ys h => rw [concat, h, concat, append]

theorem reverse_nil :
  reverse (nil : myList α) = nil :=
by
  rw [reverse]

theorem cool_theorem (x : α) (l : myList α):
  reverse (append x l) = cons x (reverse l) :=
by
  induction l with
  | nil => rw [append, reverse, reverse, reverse, append]
  | cons n l' h => rw [append, reverse, h, append, reverse]

theorem reverse_reverse (l : myList α):
  reverse (reverse l) = l :=
by
  induction l with
  | nil => rw [reverse_nil, reverse_nil]
  | cons n l' h => rw [reverse, cool_theorem n (reverse l'), h]

theorem length_append (n : α) (l : myList α):
  length (append n l) = succ (length l) :=
by
  induction l with
  | nil => rw [append, length, length, length]
  | cons x xs h => rw [append, length, h, length]

theorem length_reverse (l : myList α):
  length (reverse l) = length l :=
by
  induction l with
  | nil => rw [reverse]
  | cons x xs h => rw [reverse, length, length_append, h]

theorem length_concat_distr (xs ys : myList α) :
  length (xs ++ ys) = length xs + length ys :=
by
  induction xs with
  | nil => rw [concat, length, Nat.zero_add]
  | cons x xs h => rw [concat, length, h, length, Nat.succ_add]

theorem reverse_concat_concat_reverse (xs ys : myList α) :
  reverse (xs ++ ys) = (reverse ys) ++ (reverse xs) :=
by
  induction xs with
  | nil => rw [concat, reverse, concat_nil]
  | cons x xs h => rw [concat, reverse, h, reverse, concat_append]

theorem addNat_distr (n : Nat) (xs ys : myList Nat) :
  addNat n (concat xs ys) = (addNat n xs) ++ (addNat n ys) :=
by
  induction xs with
  | nil => rw [concat, addNat, addNat, fmap, concat]
  | cons x xs h => rw [addNat] at h
                   rw [concat, addNat, fmap,
                       h, addNat, addNat, addNat,
                       fmap, concat]

theorem concat_assoc (as bs cs : myList α) :
  concat (concat as bs) cs = concat as (concat bs cs) :=
by
  induction as with
  | nil => rw [concat, concat]
  | cons a as h => rw [concat, concat, h, concat]

theorem nil_one_id_concat (l : myList α) :
  (nil : myList α) ++ l = l ∧ l ++ (nil : myList α) = l :=
by
  refine ⟨?_, ?_⟩
  rw [concat]
  rw [concat_nil]

theorem rev_to_revcat (xs : myList α):
  (∀ (ys : myList α), (rev xs) ++ ys = revcat xs ys) :=
by
  induction xs with
  | nil => intro ys
           rw [rev, revcat, concat]
  | cons x xs h => intro l
                   rw [rev, concat_assoc,
                       concat, concat,
                       h (cons x l),
                       revcat]

-- LEVEL 4: Your own theorems

-- HW Theorems

-- Even relations
theorem false_not_true :
  false ≠ true :=
by
  intro H
  cases H

theorem lt_succ_succ_self (n : Nat) :
  n < succ (succ n) :=
by
  have h: (succ n < succ (succ n) ∨ succ n ≥ succ (succ n)) := Nat.lt_or_ge (succ n) (succ (succ n))
  apply Or.elim h
  intro h'
  have h1: (n ≤ succ n) := Nat.le_succ n
  exact Nat.lt_of_le_of_lt h1 h'
  intro h2
  have h_boom: (¬succ (succ n) ≤ succ n) := Nat.not_succ_le_self (succ n)
  exact False.elim (h_boom h2)

theorem odd_eq_not_even (n : Nat) :
  odd n = !even n :=
by
  induction n using Nat.strongInductionOn with
  | ind n ih =>
    match n with
    | 0 => rw [odd, even, Bool.not_true]
    | succ 0 => rw [even, odd, odd, even, Bool.not_false]
    | succ (succ n') =>
      rw [odd, even, even, odd, ih n' (lt_succ_succ_self n')]

theorem not_even_succ (a : Nat) :
  (!even (succ a)) = even a :=
by
  induction a using Nat.strongInductionOn with
  | ind a' ih =>
    match a' with
    | 0 => rw [even, even, odd, Bool.not_false]
    | succ 0 => rw [even, even, odd, odd, even, Bool.not_true]
    | succ (succ a') => rw [even, even, odd, odd, ih a' (lt_succ_succ_self a')]

theorem even_succ (a : Nat) :
  (!even a) = even (succ a) :=
by
  induction a using Nat.strongInductionOn with
  | ind a' ih =>
    match a' with
    | 0 => rw [even, even, odd, Bool.not_true]
    | succ 0 => rw [even, even, odd, odd, even, Bool.not_false]
    | succ (succ a') => rw [even, even, odd, odd, ih a' (lt_succ_succ_self a')]

-- Some things about Decide
theorem not_congr (h : P ↔ Q) :
  ¬P ↔ ¬Q :=
by
  apply Iff.intro
  intro np
  intro q
  suffices p : P from np p
  exact h.mpr q
  intro nq
  intro p
  suffices q : Q from nq q
  exact h.mp p

theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p := by simp

theorem decide_true {p : Prop} [Decidable p] : p → decide p :=
  (decide_iff p).2

theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1

theorem bool_iff_false {b : Bool} :
  ¬b ↔ b = false :=
by
  cases b
  apply Iff.intro
  intro
  rfl
  intro _ h'
  exact false_not_true h'
  apply Iff.intro
  intro h
  suffices h': (true = true) from False.elim (h h')
  rfl
  intro h
  exact False.elim (false_not_true h.symm)

theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1

theorem decide_false_iff (p : Prop) [Decidable p] : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))

theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1

theorem decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (decide_false_iff p).2

theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  cases h' : decide q with
  | false => exact decide_false (mt h.1 <| of_decide_false h')
  | true => exact decide_true (h.2 <| of_decide_true h')

-- Level 4.1

theorem sum_distr_concat (xs ys : myList Nat) :
  sum (concat xs ys) = sum xs + sum ys :=
by
  induction xs with
  | nil => rw [concat, sum, Nat.zero_add]
  | cons x xs h => rw [concat, sum, h, sum, Nat.add_assoc]

-- Level 4.2

theorem product_distr_concat (xs ys : myList Nat) :
  product (concat xs ys) = product xs * product ys :=
by
  induction xs with
  | nil => rw [concat, product, Nat.one_mul]
  | cons x xs h => rw [concat, product, h, product, Nat.mul_assoc]

-- Level 4.3

theorem length_concat_filter_even_odd_list (l : myList Nat):
  length (concat (filter even l) (filter odd l)) = length l :=
by
  induction l with
  | nil => rw [filter, filter, concat]
  | cons x xs h =>
    rw [filter, filter, odd_eq_not_even]
    cases even x
    rw [Bool.not_false,
        if_neg false_not_true,
        if_pos rfl, length,
        length_concat_distr,
        length, Nat.add_succ,
        ← length_concat_distr,
        h]
    rw [if_pos rfl,
        Bool.not_true,
        if_neg false_not_true,
        concat, length,
        length_concat_distr,
        length,
        ← length_concat_distr,
        h]

-- Level 4.4

theorem filter_append (n : α) (ns : myList α) (p : α → Bool):
  filter p (append n ns) = (if p n then append n (filter p ns) else (filter p ns)) :=
by
  induction ns with
  | nil => rw [filter, append, filter, filter]
  | cons x xs h =>
    rw [filter, append, filter, h]
    cases p x
    rw [if_neg false_not_true, if_neg false_not_true]
    rw [if_pos rfl, if_pos rfl, append]
    cases p n
    rw [if_neg false_not_true, if_neg false_not_true]
    rw [if_pos rfl, if_pos rfl]

theorem rev_filter_eq_filter_rev (l : myList Nat):
  reverse (filter even l) = filter even (reverse l) :=
by
  induction l with
  | nil => rw [filter, reverse, filter]
  | cons n ns h =>
    rw [filter, reverse, filter_append]
    cases even n
    rw [if_neg false_not_true, if_neg false_not_true, h]
    rw [if_pos rfl, if_pos rfl, reverse, h]

-- Level 4.5

theorem length_same_addNat (n : Nat) (l : myList Nat) :
  length (addNat n l) = length l :=
by
  induction l with
  | nil => rw [addNat, fmap]
  | cons x xs h => rw [addNat, length, fmap,
                       length, ← addNat, h]

-- Level 4.6

theorem sum_addNat (n : Nat) (l : myList Nat) :
  sum (addNat n l) = (n * length l) + sum l :=
by
  induction l with
  | nil => rw [addNat, fmap, length,
               Nat.mul_zero, Nat.zero_add]
  | cons x xs h =>
    rw [addNat] at h
    rw [addNat, fmap, sum, h,
        Nat.add_assoc,
        ← Nat.add_assoc n (n * length xs) (sum xs),
        ← Nat.mul_one n,
        Nat.mul_assoc,
        ← Nat.left_distrib,
        length,
        Nat.mul_assoc,
        Nat.left_distrib 1 (length xs) 1,
        Nat.mul_one 1,
        Nat.add_comm (1 * length xs) 1,
        sum,
        ← Nat.add_assoc (n * (1 + 1 * length xs)) x (sum xs),
        Nat.add_comm (n * (1 + 1 * length xs)) x,
        Nat.add_assoc x (n * (1 + 1 * length xs)) (sum xs)]

-- Level 4.7

theorem sum_multNat (n : Nat) (l : myList Nat) :
  sum (multNat n l) = n * sum l :=
by
  induction l with
  | nil => rw [multNat, sum, Nat.mul_zero,
               fmap, sum]
  | cons x xs h =>
    rw [multNat] at h
    rw [multNat, fmap,
        sum, h, sum,
        Nat.mul_comm x n,
        Nat.left_distrib]

-- Level 4.8

theorem product_multNat (n : Nat) (l : myList Nat) :
  product (multNat n l) = (n ^ length l) * product l:=
by
  induction l with
  | nil => rw [multNat, length, product,
               Nat.pow_zero, Nat.mul_one,
               fmap, product]
  | cons x xs h =>
    rw [multNat] at h
    rw [multNat, fmap, product, h, length, product,
        Nat.pow_succ n (length xs),
        Nat.mul_assoc (n ^ length xs) n (x * product xs),
        ← Nat.mul_assoc n x (product xs),
        Nat.mul_comm n x,
        ← Nat.mul_assoc (n ^ length xs) (x * n) (product xs),
        Nat.mul_comm (n ^ length xs) (x * n),
        Nat.mul_assoc (x * n) (n ^ length xs) (product xs)]

-- Level 4.9

theorem one_pow (m : Nat) :
  1 ^ m = 1 :=
by
  induction m with
  | zero => rw [Nat.pow_zero]
  | succ m' h => rw [Nat.pow_succ, h, Nat.mul_one]

theorem mul_pow (a b n : Nat) :
  (a * b) ^ n = (a ^ n) * (b ^ n):=
by
  induction n with
  | zero => rw [Nat.pow_zero, Nat.pow_zero,
                Nat.pow_zero, Nat.mul_one]
  | succ n' h =>
    rw [Nat.pow_succ (a * b) n', h,
        Nat.mul_assoc (a ^ n') (b ^ n') (a * b),
        Nat.mul_comm (b ^ n') (a * b),
        Nat.mul_assoc a b (b ^ n'),
        Nat.mul_comm b (b ^ n'),
        ← Nat.mul_assoc (a ^ n') a (b ^ n' * b),
        ← Nat.pow_succ a n',
        ← Nat.pow_succ b n']

theorem product_expNat (n : Nat) (l : myList Nat) :
  product (expNat n l) = (product l) ^ n :=
by
  induction l with
  | nil => rw [expNat, product,
               one_pow, fmap, product]
  | cons x xs h =>
    rw [expNat] at h
    rw [expNat, fmap,
        product, h,
        product, mul_pow]

-- Level 4.10

theorem length_matters {l l' : myList α} :
  l = l' → length l = length l' :=
by
  intro h
  rw [h]

axiom succ_inj {a b : Nat} : (succ a = succ b) → a = b
theorem not_eq_Add {n m : Nat} :
  m ≠ 0 → ¬ n = n + m :=
by
  intro h h'
  induction n with
  | zero =>
    rw [Nat.zero_add] at h'
    exact h h'.symm
  | succ n' H =>
    rw [Nat.succ_add] at h'
    exact H (succ_inj h')

theorem and_cancel_right (a b c : Bool) :
  (a && c) = (b && c) ∧ (c = true) → a = b :=
by
  intro h
  have h1: ((a && c) = (b && c)) := And.left h
  rw [(And.right h), Bool.and_true, Bool.and_true] at h1
  exact h1

theorem cons_one_neq_cons_more {x : α} :
  ∀ (n m : α) (l : myList α), ¬ cons x nil = cons n (cons m l) :=
by
  intro n m l h
  have lh: (length (cons x nil) = length (cons n (cons m l))) := length_matters h
  rw [length, length,
      length, length,
      ← Nat.zero_add (succ (length l)),
      ← Nat.succ_add] at lh
  exact not_eq_Add (Nat.succ_ne_zero (length l)) lh

theorem addNat_zero (l : myList Nat) :
  addNat zero l = l :=
by
  induction l with
  | nil => rw [addNat, fmap]
  | cons x xs h => rw [addNat] at h
                   rw [addNat, fmap, Nat.add_zero, h]

theorem add_le_add_iff {a b n : Nat}  :
  a + n ≤ b + n ↔ a ≤ b :=
by
  apply Iff.intro
  intro h
  induction n with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero] at h
    exact h
  | succ n' h' =>
    rw [Nat.add_succ, Nat.add_succ] at h
    suffices h'': (a + n' ≤ b + n') from h' h''
    exact Nat.le_of_succ_le_succ h
  intro h
  induction n with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero]
    exact h
  | succ n' h' =>
    rw [Nat.add_succ, Nat.add_succ]
    exact Nat.succ_le_succ h'

theorem isSorted_addNat (n : Nat) (l : myList Nat) :
  isSorted (addNat n l) = isSorted l :=
by
  induction l with
  | nil => rw [addNat, fmap]
  | cons x xs h =>
    rw [addNat] at h
    rw [addNat]
    cases xs with
    | nil =>
      rw [fmap, isSorted, isSorted]
      exact cons_one_neq_cons_more
      exact cons_one_neq_cons_more
    | cons y ys =>
      rw [fmap] at h
      rw [fmap, fmap, isSorted, h, isSorted]
      rw [decide_congr add_le_add_iff]

-- Level 4.11

theorem or_inl {a b : Bool} (H : a) : a || b :=
by
  rw [or, H]

theorem or_comm : ∀ a b, (a || b) = (b || a) :=
by
  intro a b
  cases a
  cases b
  rfl
  rw [or, or]
  cases b
  rw [or, or]
  rfl

theorem or_inr {a b : Bool} (H : b) : a || b :=
by
  rw [or_comm, or_inl H]

theorem even_Add (a b : Nat) :
  even (a + b) = ((even a && even b) || (odd a && odd b)) :=
by
  induction a using Nat.strongInductionOn with
  | ind a' ih =>
    match a' with
    | 0 =>
      rw [Nat.zero_add, odd_eq_not_even, odd_eq_not_even]
      cases even b
      rw [Bool.and_false, Bool.not_false,
          Bool.and_true, even, Bool.false_or,
          Bool.not_true]
      rw [even, Bool.and_self, Bool.true_or]
    | succ 0 =>
      rw [Nat.succ_add, Nat.zero_add,
          odd_eq_not_even, odd_eq_not_even,
          ← even_succ]
      cases even b
      rw [Bool.not_false, even, odd, Bool.false_and,
          Bool.not_false, Bool.and_true,
          Bool.or_true]
      rw [Bool.not_true, even, odd, Bool.false_and,
          Bool.and_false, Bool.or_false]
    | succ (succ a') =>
      rw [Nat.succ_add (succ a') b,
          Nat.succ_add a' b, odd,
          even, even, odd, odd, even,
          ih a' (lt_succ_succ_self a')]


theorem odd_Add (a b : Nat) :
  odd (a + b) = ((even a && odd b) || (odd a && even b)) :=
by
  rw [odd_eq_not_even, even_Add, odd_eq_not_even, odd_eq_not_even]
  cases even a
  rw [Bool.false_and, Bool.not_false,
      Bool.true_and, Bool.false_and,
      Bool.true_and, Bool.false_or,
      Bool.false_or, Bool.not_not]
  rw [Bool.true_and, Bool.not_true,
      Bool.false_and, Bool.or_false,
      Bool.true_and, Bool.false_and,
      Bool.or_false]

theorem not_and (b : Bool) :
  (!b && b) = false :=
by
  cases b
  rw [Bool.and_false]
  rw [Bool.not_true, Bool.false_and]

theorem and_comm (a b : Bool) :
  (a && b) = (b && a) :=
by
  cases a
  rw [Bool.and_false, Bool.false_and]
  rw [Bool.and_true, Bool.true_and]

theorem and_not (b : Bool) :
  (b && !b) = false :=
by
  rw [and_comm, not_and]

theorem my_simp (a b c : Bool) :
  (a && (b && (b && (c || !c) || !b && (c && !c || !c && c)) ||
  !b && (b && (c && !c || !c && c) || !b && (c && c || !c && !c))) ||
  !a && (b && (b && (c && !c || !c && c) || !b && (c && c || !c && !c)) ||
  !b && (b && (c && c || !c && !c) || !b && (c && !c || !c && c))))
  = (a && (c && c || !c && !c) || !a && (c && !c || !c && c)) :=
by
  rw [not_and, and_not,
      Bool.or_false, Bool.and_false,
      Bool.and_false, Bool.and_false,
      Bool.false_or, Bool.or_false, Bool.or_false,
      Bool.or_false]
  cases b
  rw [Bool.not_false, Bool.false_and,
      Bool.false_and, Bool.false_and,
      Bool.and_false, Bool.or_false,
      Bool.and_false, Bool.true_and,
      Bool.false_or, Bool.true_and,
      Bool.or_false]
  rw [Bool.not_true, Bool.false_and,
      Bool.false_and, Bool.and_false,
      Bool.false_and, Bool.false_or,
      Bool.true_and, Bool.true_and,
      Bool.and_false, Bool.or_false,
      Bool.or_false, Bool.and_self,
      Bool.and_self]

theorem even_succ_succ_product (a b : Nat) :
  even ((succ (succ a)) * b) = even (a * b) :=
by
  match b with
  | 0 => rw [Nat.mul_zero, Nat.mul_zero]
  | succ 0 =>
    rw [Nat.mul_succ, Nat.mul_zero,
        Nat.add_succ 0 (succ a),
        Nat.add_succ 0 a,
        Nat.mul_succ, Nat.mul_zero,
        Nat.zero_add, even, odd]
  | succ (succ b') =>
    rw [Nat.mul_succ, Nat.mul_succ,
        Nat.mul_succ, Nat.mul_succ,
        Nat.succ_mul, Nat.succ_mul,
        Nat.add_assoc, Nat.add_assoc,
        Nat.add_assoc, Nat.add_assoc,
        even_Add, even_Add,
        even_Add, even_Add,
        even_Add, odd,
        odd_Add, odd_Add,
        odd_Add, odd_Add,
        odd_Add, odd_Add,
        odd_Add, even,
        odd, even_Add,
        even_Add, even_Add,
        even_Add, odd_Add,
        even, odd,
        Bool.and_self,
        Bool.and_self,
        odd_eq_not_even,
        odd_eq_not_even, even,
        odd_eq_not_even, even,
        odd, even, even, odd,
        Bool.and_false,
        Bool.false_or, Bool.not_true,
        Bool.not_false, Bool.and_true,
        odd_eq_not_even, odd_eq_not_even,
        odd_eq_not_even, even_Add,
        odd_eq_not_even]
    rw [my_simp]

theorem even_product (x y : Nat) :
  even (x * y) = (even x || even y) :=
by
  induction x using Nat.strongInductionOn with
  | ind x' ih =>
    match x' with
    | 0 => rw [Nat.zero_mul, even, Bool.true_or]
    | 1 => rw [Nat.one_mul, even, odd, Bool.false_or]
    | succ (succ k) =>
      rw [even, even_succ_succ_product, odd, ih k (lt_succ_succ_self k)]

theorem even_list_product (l : myList Nat) :
  even (product l) = Any even l :=
by
  induction l with
  | nil => rw [product, even, odd, Any]
  | cons x xs h =>
    rw [product, Any, even_product, h]

-- Level 4.12

theorem even_sum_even_length_filter_odd (l : myList Nat) :
  even (sum l) = even (length (filter odd l)) :=
by
  induction l with
  | nil => rw [sum, filter, length]
  | cons x xs h =>
    rw [filter, sum, even_Add, odd_eq_not_even, odd_eq_not_even, h]
    cases even x
    rw [if_pos Bool.not_false,
        Bool.not_false,
        Bool.false_and,
        Bool.true_and,
        Bool.false_or,
        length,
        even_succ]
    rw [Bool.not_true,
        if_neg false_not_true,
        Bool.false_and,
        Bool.true_and,
        Bool.or_false]

-- Level 4.13

theorem zero_Add_eq_zero_and_zero (a b : Nat) :
  Zero (a + b) = (Zero a && Zero b) :=
by
  cases a with
  | zero =>
    rw [Nat.zero_add]
    cases Zero b
    rw [Bool.and_false]
    rw [Bool.and_true, Zero]
  | succ a' =>
    rw [Nat.succ_add]
    cases Zero b
    rw [Zero, Bool.and_false]
    rfl
    rw [Bool.and_true, Zero, Zero]
    rfl

theorem zero_sum_all_zero (l : myList Nat) :
  Zero (sum l) = All Zero l :=
by
  induction l with
  | nil => rw [sum, All, Zero]
  | cons x xs h =>
    rw [sum, All, zero_Add_eq_zero_and_zero, h]

-- Level 4.14

theorem zero_succ_false (a : Nat) :
  Zero (succ a) = false :=
by
  rw [Zero]
  rfl

theorem zero_Mult_eq_zero_or_zero (a b : Nat) :
  Zero (a * b) = (Zero a || Zero b) :=
by
  cases a with
  | zero => rw [Nat.zero_mul, or, Zero]
  | succ a' =>
    cases b with
    | zero => rw [Nat.mul_zero, Zero, Zero, Bool.or_true]
    | succ b' =>
      rw [Nat.mul_succ,
          Nat.succ_mul,
          zero_Add_eq_zero_and_zero,
          zero_Add_eq_zero_and_zero,
          Bool.and_assoc,
          zero_succ_false,
          zero_succ_false,
          Bool.and_false,
          Bool.and_false]
      rfl

theorem zero_product_any_zero (l : myList Nat) :
  Zero (product l) = Any Zero l :=
by
  induction l with
  | nil => rw [product, Any, Zero]
  | cons x xs h =>
    rw [product,
        Any,
        zero_Mult_eq_zero_or_zero,
        h]

-- Level 4.15

theorem addNat_Add (n m : Nat) (l : myList Nat) :
  addNat (n + m) l = addNat n (addNat m l) :=
by
  induction l with
  | nil => rw [addNat, fmap, addNat, addNat, fmap, fmap]
  | cons x xs h =>
    rw [addNat] at h
    rw [addNat, fmap, h,
        addNat, addNat,
        addNat, addNat,
        fmap, fmap,
        Nat.add_assoc,
        Nat.add_comm m n]

-- Level 4.16

theorem multNat_Mult (n m : Nat) (l : myList Nat) :
  multNat (n * m) l = multNat n (multNat m l) :=
by
  induction l with
  | nil => rw [multNat, fmap, multNat, multNat, fmap, fmap]
  | cons x xs h =>
    rw [multNat] at h
    rw [multNat, fmap, h,
        multNat, multNat,
        multNat, multNat,
        fmap, fmap,
        Nat.mul_assoc,
        Nat.mul_comm m n]
