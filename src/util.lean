import tactic.ring

notation `rel` α := α -> α -> Prop

namespace nat
lemma add_le_left_right : ∀ n m k l : nat, n ≤ m → k ≤ l → n + k ≤ m + l :=
begin intros
, transitivity (n + l)
, {apply (nat.add_le_add_left a_1)}
, {apply (nat.add_le_add_right a)}
end

end nat

namespace list

def split_with 
  {α : Type} (f : α → Prop) 
  [decidable_pred f] 
  : list α -> (list α × list α)
| [] := ([],[])
| (x::xs) := 
  match split_with xs with (f_true, f_false) := 
    if f x 
      then (x :: f_true, f_false)
      else (f_true, x :: f_false)
  end

lemma split_with_is_filter 
  (α : Type) (f : α -> Prop) [decidable_pred f] (l : list α) : 
  split_with f l = (filter f l, filter (not ∘ f) l) :=
  begin intros
  , induction l
  , 
    { simp [split_with, filter] }
  , 
    { simp [split_with, filter]
    , rewrite l_ih
    , tactic.unfreeze_local_instances
    , simp [decidable_pred] at _inst_1
    , simp [split_with._match_1]
    , have f_l_hd_dec : decidable (f l_hd)
    , 
      {apply _inst_1}
    , by_cases (f l_hd)
    , 
      { rewrite if_pos
      , rewrite if_pos
      , rewrite if_neg
      , apply (not_not_intro h)
      , all_goals {assumption}
      }
    , 
      { rewrite if_neg
      , rewrite if_neg
      , rewrite if_pos
      , all_goals {assumption}
      }
    }
  end

lemma filter_sizeof 
{α} [has_sizeof α] (f : α → Prop) [decidable_pred f] (l : list α)
  : sizeof (filter f l) ≤ sizeof l :=
begin intros
, induction l
, {simp [filter]}
, by_cases (f l_hd)
, { rewrite (list.filter_cons_of_pos _ h)
  , simp [sizeof, has_sizeof.sizeof, list.sizeof] at *
  , assumption
  }
, { rewrite (list.filter_cons_of_neg _ h)
  , simp [sizeof, has_sizeof.sizeof, list.sizeof] at *
  , transitivity (list.sizeof l_tl)
  , {exact l_ih}
  , rewrite <- add_assoc
  , apply nat.le_add_left
  }
end

end list

namespace fin

def zero_on_up : ∀ {n}, list (fin n)
| 0 := []
| (m+1) := 0 :: list.map fin.succ (@zero_on_up m)

end fin

export list