-- /-Partitions Part 1-/

-- import util
-- import tactic.ring

-- section partition_type

-- parameter α : Type

-- structure partition := 
--   (equiv : α -> α -> Prop) 
--   (is_equiv : is_equiv _ equiv) 
--   (non_vacous : inhabited α)
--   (decidable : Π x, decidable_pred (equiv x))

-- def refines (pl pr : partition) := ∀ x y, pr.equiv x y -> pl.equiv x y

-- lemma refines_refl : ∀ p, refines p p
-- | p := begin simp [refines] end

-- lemma refines_trans : ∀ a b c, refines a b -> refines b c -> refines a c :=
--   begin simp [refines], intros a b c ab bc x y H
--               , apply (ab x y (bc x y H)) end

-- instance partition_preorder : preorder partition :=
-- {preorder 
-- . le := refines
-- , le_refl := refines_refl
-- , le_trans := refines_trans
-- }

-- end partition_type

-- section fin_partition

-- notation `part` n := partition (fin n)

-- section part_to_boxes

-- variable {n : ℕ}
-- variable r : rel (fin n)
-- variable [∀ x : fin n, decidable_pred (r x)]

-- def go : finset (fin n) -> finset (finset (fin n))
-- | [] := []
-- | (x :: xs) :=
--   have H : 
--     finset.sizeof ((split_with (r x) xs).snd) < fin.sizeof n x + (1 + finset.sizeof xs)
--     , begin intros
--       , rewrite list.split_with_is_filter
--       , simp
--       , apply (@lt_of_le_of_lt _ _ _ (sizeof xs))
--       , all_goals {simp [sizeof, has_sizeof.sizeof]}
--       , { apply list.filter_sizeof }
--       , { apply (@nat.lt_of_le_of_lt _ (list.sizeof xs + sizeof x))
--         , apply (nat.le_add_right (list.sizeof xs) (sizeof x))
--         , rewrite <- add_assoc
--         , rewrite (add_comm _ 1)
--         , simp [sizeof, has_sizeof.sizeof]
--         , rewrite nat.lt_succ_iff
--         }
--       end
--   , let pair := split_with (r x) xs in
--     (x :: pair.fst) :: go pair.snd

-- end part_to_boxes

-- def part_to_boxes {n} (p : part n) : list (list (fin n)) :=  
--   @go n (p.equiv) p.decidable fin.zero_on_up 

-- def part_to_string {n} (p : part n) : string := 
--   (list.to_string (part_to_boxes p))

-- def boxes_to_part -- the on_objects of the free functor from lists of lists to partitions

-- def part_enum : ∀ n, list (part n) := 

-- end fin_partition
