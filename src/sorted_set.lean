--
-- This defines finite sorted sets
-- , an efficient implrementation of finite sets
-- , for oredered types

-- imports
import order.lattice

import order
import util
import algebra.order

definition increasing {α} [partial_order α] := chain' (λ x y : α, x < y)

structure sset (α : Type) := 
  -- stuff 
  (val : list α)
  -- properties 
  (increasing [partial_order α] : increasing val)

namespace sset

instance sset_has_mem 
  : ∀ {α}, has_mem α (sset α) :=
  λ α, {has_mem . mem := λ x s, x ∈ s.val}

def to_set (α) [partial_order α] : sset α → set α
| s := λ x : α, x ∈ s

def subset {α} : rel (sset α)
| a b := list.subset a.val b.val

def subset_trans {α} : transitive (@subset α) :=
begin unfold transitive
, simp [subset, list.subset]
, intros
, repeat {apply_assumption}
end

instance sset_partial_order (α) [partial_order α] 
  : partial_order (sset α) :=
{ partial_order
. le := sset.subset
, le_refl := 
  begin intro
  , dsimp [subset, list.subset]
  , intros α H, exact H
  end
, le_trans := subset_trans
, lt := 
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