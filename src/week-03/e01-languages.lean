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
  sorry,
end

@[simp] lemma mul_zero (L : set (list α)) : L * 0 = 0 :=
begin
  sorry,
end

@[simp] lemma append_one (A : set (list α)) : A * 1 = A :=
begin
  apply subset.antisymm, {
    sorry,
  }, {
    sorry,
  },
end

@[simp] lemma one_append (A : set (list α)) : 1 * A = A :=
begin
  sorry,
end

lemma append_assoc (A B C : set (list α)): 
    (A * B) * C = A * (B * C) :=
begin
  sorry,
end

lemma left_distrib (A B C : set (list α)) : A * (B + C) = A * B + A * C :=
begin
  sorry,
end

lemma right_distrib (A B C : set (list α)) : (A + B) * C = A * C + B * C :=
begin
  sorry,
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
  sorry,
end

lemma pow_subset_of_subset {A B : set (list α)} {n : ℕ} : A ⊆ B → A^n ⊆ B^n :=
begin
  sorry,
end

lemma contain_eps_subset_power {A : set (list α)} {n : ℕ} (h : 1 ⊆ A) : A ⊆ A^(n.succ) :=
begin
  sorry,
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
  sorry,
end

@[simp] lemma one_subset_star : 1 ⊆ star L :=
begin    
  simp,
end

@[simp] lemma pow_subset_star (n : ℕ) : L^n ⊆ star L :=
begin
  sorry,
end

@[simp] lemma subset_star : L ⊆ star L :=
begin
  sorry,
end

lemma star_subset_star : L ⊆ M → star L ⊆ star M :=
begin
  sorry,
end

lemma append_subset_star {A B L : set (list α)} : 
    A ⊆ star L → B ⊆ star L → (A * B) ⊆ star L :=
begin
  sorry,
end

lemma star_append_star_eq_star : star L * star L = star L :=
begin
  sorry,
end 

lemma pow_star_eq_star (n : ℕ) : (star L)^n.succ = star L :=
begin
  sorry,
end

-- Это было в ДЗ по дискретке!                
theorem star_star_eq_star : star (star L) = star L :=
begin
  sorry,
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
  sorry,
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
  sorry,
end

lemma mem_star_iff_list_join {w : list α} :
  w ∈ star L ↔ ∃ l (h : ∀ x ∈ l, x ∈ L), w = list.join l :=
begin
  rw star_eq_list_join,
  refl,
end

-- Еще одно ДЗ из курса формальных языков
lemma union_star_eq_star_mul_star_star : star (L + M) = star (star L * star M) :=
begin
  sorry,
end

lemma mul_star_subset_star : L * star L ⊆ star L :=
begin
  sorry,
end

-- Решаем уравнения в языках: если [] ∉ A, то L = A * L + B ↔ L = star A * b
lemma linear_eq_iff {A B : set (list α)} (hnil : [] ∉ A) : L = A * L + B ↔ L = star A * B :=
begin
  sorry,
end

end languages