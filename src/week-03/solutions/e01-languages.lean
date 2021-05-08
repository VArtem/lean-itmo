import data.set.basic
import data.list.basic
import tactic

open set list

-- Будем рассматривать языкы над алфавитом α
-- Язык это просто set (list α)
namespace languages

variables {α : Type} {L M : set (list α)}


-- Несколько удобных сокращений: ε = пустой список, 0 = ∅, 1 = {ε}, A + B = A ∪ B 
def ε {α} : list α := [] 
instance : has_zero (set (list α)) := ⟨(∅ : set _)⟩
instance : has_one (set (list α)) := ⟨({[]} : set _)⟩
instance : has_add (set (list α)) := ⟨set.union⟩

-- Конкатенация языков состоит из таких слов `w`, что существуют слова `left ∈ L` и `right ∈ M`, что `w = left ++ right`)
def append (L M: set (list α)) := 
    { w : list α | ∃ (left ∈ L) (right ∈ M), w = left ++ right}

-- Будем обозначать умножение как `L * M`
instance : has_mul (set (list α)) := ⟨append⟩

-- И вспомогательные леммы
@[simp] def zero_def : (0 : set (list α)) = ∅ := rfl
@[simp] def one_def : (1 : set (list α)) = {[]} := rfl
@[simp] def mem_zero {w : list α} : w ∉ (0 : set (list α)) := by simp
@[simp] def mem_one {w : list α} : w ∈ (1 : set (list α)) ↔ w = [] := by refl
@[simp] def nil_mem_one : [] ∈ (1 : set (list α)) := by simp


-- Умелое использование `rcases` и `rintro` сильно вам поможет!
@[simp] lemma zero_mul (L : set (list α)) : 0 * L = 0 :=
begin
  ext w, split, {
    rintro ⟨left, hleft, right, hright, rfl⟩,
    simpa only using hleft,
  }, {
    intro h,
    exact absurd h mem_zero,
  }
end

@[simp] lemma mul_zero (L : set (list α)) : L * 0 = 0 :=
begin
  ext w, split, {
    rintro ⟨left, hleft, right, hright, rfl⟩,
    simpa only using hright,
  }, {
    intro h,
    exact absurd h mem_zero,
  }
end

@[simp] lemma append_one (A : set (list α)) : A * 1 = A :=
begin
  apply subset.antisymm, {
    rintro _ ⟨left, right, hleft, hright, rfl⟩,
    rw mem_one at hright,
    rwa [hright, list.append_nil],
  }, {
    rintro x xa,
    use [x, xa],
    use [[], nil_mem_one],
    exact (append_nil x).symm,
  },
end

@[simp] lemma one_append (A : set (list α)) : 1 * A = A :=
begin
  apply subset.antisymm, {
    rintro _ ⟨ left, hleft, right, hright, rfl ⟩,
    rw mem_one at hleft,
    rwa [hleft, list.nil_append],
  }, {
    rintro x xa,
    use [[], nil_mem_one, x, xa],
    exact (nil_append x).symm,
  },
end

lemma append_assoc (A B C : set (list α)): 
    (A * B) * C = A * (B * C) :=
begin
  apply subset.antisymm, {
    rintro _ ⟨_, ⟨left, hleft, mid, hmid, rfl ⟩, right, hright, rfl ⟩,
    use [left, hleft],
    use [mid ++ right],
    use [mid, hmid, right, hright],
    exact append_assoc left mid right,
  }, {
    rintro _ ⟨left, hleft, _, ⟨mid, hmid, right, hright, rfl⟩, rfl ⟩,
    refine ⟨left ++ mid, ⟨left, hleft, mid, hmid, rfl⟩, right, hright, _⟩,
    exact (append_assoc left mid right).symm,
  },
end

lemma left_distrib (A B C : set (list α)) : A * (B + C) = A * B + A * C :=
begin
  ext w, split, {
    rintro ⟨left, hleft, right, (hB | hC), rfl⟩,
    { left, exact ⟨left, hleft, right, hB, rfl⟩ },
    { right, exact ⟨left, hleft, right, hC, rfl⟩ },
  }, {
    rintro (⟨left, hleft, right, hB, rfl⟩ | ⟨left, hleft, right, hC, rfl⟩),
    { exact ⟨left, hleft, right, (or.inl hB), rfl⟩, },
    { exact ⟨left, hleft, right, (or.inr hC), rfl⟩, },
  }
end

lemma right_distrib (A B C : set (list α)) : (A + B) * C = A * C + B * C :=
begin
    ext w, split, {
    rintro ⟨left, (hA | hB), right, hright, rfl⟩,
    { left, exact ⟨left, hA, right, hright, rfl⟩ },
    { right, exact ⟨left, hB, right, hright, rfl⟩ },
  }, {
    rintro (⟨left, hA, right, hright, rfl⟩ | ⟨left, hB, right, hright, rfl⟩),
    { exact ⟨left, (or.inl hA), right, hright, rfl⟩, },
    { exact ⟨left, (or.inr hB), right, hright, rfl⟩, },
  }
end

-- Докажем, что множество языков с операциями + = ∪ и * = append образуют полукольцо:
-- A + B - коммутативный моноид: 0, ассоциативность, коммутативность
-- A * B - полугруппа: 1, ассоциативность
-- Дистрибутивность и умножение на 0
-- Свойства (+) можно достать из стандартной библиотеки про `set.union`, а свойства (*) пришлось доказать
instance : semiring (set (list α)) := {
  add := (+),
  add_assoc := set.union_assoc,
  zero := 0,
  zero_add := set.empty_union,
  add_zero := set.union_empty,
  add_comm := set.union_comm,
  mul := (*),
  mul_assoc := append_assoc,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  one := 1,
  one_mul := one_append,
  mul_one := append_one,
  left_distrib := left_distrib,
  right_distrib := right_distrib,
}

-- Теперь можно использовать L^n = L * L * ... * L (n раз)
-- Полезные леммы: `pow_zero`, `pow_succ`, `pow_add`, ...

lemma append_subset_of_subset {A B C D : set (list α)} : A ⊆ C → B ⊆ D → A * B ⊆ C * D :=
begin
  rintro hAC hBD x ⟨left, hleft, right, hright, rfl⟩,
  use [left, hAC hleft, right, hBD hright],
end

lemma pow_subset_of_subset {A B : set (list α)} {n : ℕ} : A ⊆ B → A^n ⊆ B^n :=
begin
  intro hAB,
  induction n with n ih, {
      simp only [pow_zero],
  }, {
    rw [pow_succ, pow_succ],
    refine append_subset_of_subset hAB ih,
  },
end

lemma contain_eps_subset_power {A : set (list α)} {n : ℕ} (h : 1 ⊆ A) : A ⊆ A^(n.succ) :=
begin
  induction n with n ih, {
    rw pow_one, 
  }, {
    rw pow_succ,
    nth_rewrite 0 ←one_append A,
    refine append_subset_of_subset h ih,
  }
end

-- Замыкание Клини языка L равно объединению L^n по всем натуральным n
def star (L : set (list α)) := {w : list α | ∃ (n : ℕ), w ∈ L^n}

@[simp] lemma mem_star {w : list α} : w ∈ star L ↔ ∃ (n : ℕ), w ∈ L^n := by refl

lemma star_eq_Union : star L = ⋃ (n : ℕ), L^n :=
begin
  ext w, simp only [mem_Union, mem_star],
end

@[simp] lemma nil_mem_star : [] ∈ star L :=
begin
  use 0,
  simp only [set.mem_singleton, one_def, pow_zero],
end

@[simp] lemma one_subset_star : 1 ⊆ star L :=
begin    
  simp,
end

@[simp] lemma pow_subset_star (n : ℕ) : L^n ⊆ star L :=
begin
  rw star_eq_Union,
  refine subset_Union _ _,
end

@[simp] lemma subset_star : L ⊆ star L :=
begin
  -- сделает `rw` только в левой части
  conv_lhs {rw ← pow_one L},
  exact pow_subset_star 1,
end

lemma star_subset_star : L ⊆ M → star L ⊆ star M :=
begin
  rintro hAB w ⟨n, ha⟩,
  use n,
  exact pow_subset_of_subset hAB ha,
end

lemma append_subset_star {A B L : set (list α)} : 
    A ⊆ star L → B ⊆ star L → (A * B) ⊆ star L :=
begin
  rintro al bl _ ⟨left, hleft, right, hright, rfl⟩,
  rcases al hleft with ⟨an, ah⟩,
  rcases bl hright with ⟨bn, bh⟩,
  use an + bn,
  rw pow_add,
  use [left, ah, right, bh],
end

lemma star_append_star_eq_star : star L * star L = star L :=
begin
  apply subset.antisymm, {
    apply append_subset_star (set.subset.refl _) (set.subset.refl _),
  }, {
    conv_lhs {rw ← mul_one (star L)},
    apply append_subset_of_subset,
    { refl },
    { exact one_subset_star },
  }
end 

lemma pow_star_eq_star (n : ℕ) : (star L)^n.succ = star L :=
begin
  induction n with n ih, {
    rw [pow_one],
  }, {
    apply subset.antisymm, {
      rw [pow_succ, ih, star_append_star_eq_star],
    }, {
      apply contain_eps_subset_power,
      exact one_subset_star,
    },
  },
end

-- Это было в ДЗ по дискретке!                
theorem star_star_eq_star : star (star L) = star L :=
begin
  apply subset.antisymm, {
    rintro x ⟨n, hx⟩,
    cases n,
    { rw [pow_zero] at hx, apply one_subset_star hx },
    { rwa pow_star_eq_star at hx }
  }, {
    exact subset_star,
  },
end

-- L^n равен множеству слов, которые можно получить, как конкатенацию `n` слов из `L`. 
-- Как записать, что `w` представляется как конкатенация `n` слов из `L`?
-- `∃ (l : list (list α)) (h : ∀ x ∈ l, x ∈ L), w = list.join l ∧ l.length = n`
-- Буквально: существует список слов `l`, что все слова в `l` принадлежат `L`, `w` равен `list.join l`, и длина `l` равна `n`
-- Начались сложные задания! Изучите подробнее API `list`, `list.has_mem`, `list.join` и прочие полезные вещи, или увереннее используйте `simp` :)
#check list.mem
#check mem_cons_self
#check list.join
#check join_eq_nil

lemma pow_eq_list_join {n : ℕ} : 
    L^n = {w | ∃ (l : list (list α)) (h : ∀ x ∈ l, x ∈ L), w = list.join l ∧ l.length = n} :=
begin
  apply subset.antisymm, {
    induction n with n ih, {
      simp,
      use [[]],
      simp,
    }, {
      rw pow_succ,
      rintro _ ⟨left, hleft, right, hright, rfl⟩,
      obtain ⟨tail, hmem, rfl, rfl⟩ := ih hright,
      clear ih,
      simp,
      refine ⟨left :: tail, _, _, _⟩,
      -- Стало 3 цели: 1. все элементы списка лежат в L
      -- 2. join ведет себя по определению - `refl`
      -- 3. длина списка на 1 больше - `refl`
      { rintro x (rfl | xtail),
        { exact hleft, },
        { exact hmem _ xtail, },
      },
      { refl },
      { refl },
    }
  }, {
    induction n with n ih, {
      simp,
      rintro w l h rfl hlen,
      rw [length_eq_zero] at hlen,
      subst hlen,
      refl,
    }, {
      rintro w ⟨l, hmem, rfl, hlen⟩,
      rw pow_succ,
      -- Докажем, что l не пустой, потому что l.length = n.succ
      cases l with head tail,
      { exfalso, exact (ne_nil_of_length_eq_succ hlen) rfl, },
      rw [join],
      -- Осталось показать, что `head ∈ L` и `tail.join ∈ L^n`
      refine ⟨head, _, tail.join, _, rfl⟩, {
        apply hmem,
        apply mem_cons_self,
      }, {
        apply ih,
        simp,
        refine ⟨tail, _, _, _⟩,
        { rintro x xtail,
          apply hmem x,
          exact mem_cons_of_mem _ xtail, },
        { refl, },
        { simpa [nat.add_one] using hlen, },
      }
    }
  }
end

lemma mem_pow_iff_list_join {w : list α} {n : ℕ} 
  : w ∈ L^n ↔ ∃ l (h : ∀ x ∈ l, x ∈ L), w = list.join l ∧ l.length = n :=
begin
  rw pow_eq_list_join,
  refl,
end

-- Замыкание Клини - все слова, которые можно представить как конкатенацию слов из L (без ограничения на количество)
lemma star_eq_list_join : 
  star L = {w | ∃ l (h : ∀ x, x ∈ l → x ∈ L), w = list.join l} :=
begin
  ext w, split, {
    rintro ⟨n, hw⟩,
    rw pow_eq_list_join at hw,
    rcases hw with ⟨l, h, rfl, rfl⟩,
    use [l, h],
  }, {
    rintro ⟨l, h, rfl⟩,
    apply pow_subset_star l.length,
    rw [pow_eq_list_join],
    refine ⟨l, h, rfl, rfl⟩,
  }
end

lemma mem_star_iff_list_join {w : list α} :
  w ∈ star L ↔ ∃ l (h : ∀ x ∈ l, x ∈ L), w = list.join l :=
begin
  rw star_eq_list_join,
  refl,
end

-- Еще одно ДЗ
lemma union_star_eq_star_mul_star_star : star (L + M) = star (star L * star M) :=
begin
  apply subset.antisymm, {
    apply star_subset_star,
    apply union_subset, {
      conv_lhs {rw ←mul_one L},
      apply append_subset_of_subset (subset_star) (one_subset_star),
    }, {
      conv_lhs {rw ←one_mul M},
      apply append_subset_of_subset (one_subset_star) (subset_star),      
    }
  }, {
    rw [star_eq_Union, Union_subset_iff],
    rintro n,
    induction n with n ih, {
      simp,
    }, {
      rw [pow_succ],
      apply append_subset_star,
      apply append_subset_star,
      { apply star_subset_star, exact subset_union_left _ _, },
      { apply star_subset_star, exact subset_union_right _ _, },
      { exact ih, },
    }
  }
end

lemma mul_star_subset_star : L * star L ⊆ star L :=
begin
  rintro _ ⟨left, hleft, right, ⟨n, hright⟩, rfl⟩,
  apply pow_subset_star (1 + n),
  rw [pow_add, pow_one],
  exact ⟨left, hleft, right, hright, rfl⟩,
end

-- Решаем уравнения в языках: если [] ∉ A, то L = A * L + B ↔ L = star A * b
lemma linear_eq_iff {A B : set (list α)} (hnil : [] ∉ A) : L = A * L + B ↔ L = star A * B :=
begin
  sorry,
end

end languages