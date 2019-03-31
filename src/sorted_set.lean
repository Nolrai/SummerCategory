--
-- This defines finite sorted sets
-- , an efficient implrementation of finite sets
-- , for oredered types

-- imports
import order.lattice

import order
import util
import algebra.order

definition increasing {α} [partial_order α] := 
  chain' (λ x y : α, x < y)

section

variables (α : Type) [partial_order α] 

structure sset := 
  -- stuff 
  (val : list α)
  -- properties 
  (val_increasing : increasing val)

end

variables {α : Type} [partial_order α]

namespace sset

def increasing_nil : increasing (nil : list α) :=
begin simp [increasing] end 

instance sset_has_emptyc (n : ℕ) : has_emptyc (sset (fin n)) :=
has_emptyc.mk ⟨[] , increasing_nil⟩ 

def monotone {β} (f : α → β) [partial_order β] 
  : Prop := ∀ x y, x ≤ y → f x ≤ f y

def sset_ord_cons 
  : ∀ (x y : α) (ys : list α)
  , x < y → increasing (y :: ys) → increasing (x :: y :: ys) :=
begin intros _ _ _ _
, simp [increasing]
, simp [chain']
, intro
, split; assumption
end

section

variables
  (C : list α -> Prop)
  (c_nil : C nil)
  (c_singleton : ∀ x, C [x])

variable (c_inductive : ∀ x y l, x < y -> C (y :: l) -> C (x :: y :: l))

lemma increasing_induction'
  (c_inductive : ∀ x y l, x < y → C (y :: l) -> C (x :: y :: l))
  : ∀ n l, length l = n -> increasing l -> C l 
| (n +2) (x :: y :: xs) length_h p :=
  begin simp [increasing, chain'] at * 
  , apply (c_inductive x y xs); cases p
  , assumption
  , apply (increasing_induction' (n+1))
  , simp [length]
  , ring at *
  , have h : length xs = n
  , apply (nat.add_right_cancel length_h)
  , rewrite h
  , unfold chain'
  , apply p_right
  end
| 1 [x] _ _ := c_singleton x
| 0 [] _ _ := c_nil 
  
end

def all_fin : ∀ n, sset (fin n)
| 0 := ∅ 
| (n + 1) := 
  ⟨map (fin.succ) (all_fin n).val
  , begin simp [increasing, map ] end⟩ 

instance sset_has_mem 
  : has_mem α (sset α) :=
  {has_mem . mem := λ x s, x ∈ s.val}

def to_set : sset α → set α
| s := λ x : α, x ∈ s

def subset : rel (sset α)
| a b := list.subset a.val b.val

def subset_trans : transitive (@subset α _inst_1) :=
begin unfold transitive
, simp [subset, list.subset]
, intros
, repeat {apply_assumption}
end

#print prefix list

def subset_antisymm (x y : sset α) : subset x y → subset y x → x = y :=
begin simp [subset]
, cases x; cases y
, simp at *
, cases x_val_increasing 
end

instance sset_preorder (α) [partial_order α] 
  : partial_order (sset α) :=
{ partial_order
. le := sset.subset
, le_refl := 
  begin intro
  , dsimp [subset, list.subset]
  , intros α H, exact H
  end
, le_trans := subset_trans
, le_antisymm := 'a'
}

open lattice

def union {α : Type} : ∀ (_ _ : sset α), sset α
| ⟨[], _⟩ b := b
| a  ⟨[], _⟩ := a
| ⟨x :: xs, x_p⟩ ⟨ y :: ys, P⟩ :=
  if x < y
    then 

instance semilattice_sup (α : Type) [partial_order α] 
  : semilattice_sup (sset α) :=
{ semilattice_sup
. sup := union
}


instance sset_lattice (α : Type) [partial_order α] : lattice (sset α) :=
{ lattice 
}

end sset