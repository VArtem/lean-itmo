import data.set.basic
import data.set.lattice

/-
Первые несколько строк файла на Lean импортируют нужные файлы. Если вы скачали репозиторий с помощью `leanproject`, то у вас автоматически в _target/deps/mathlib установлена библиотека mathlib:
GitHub: https://github.com/leanprover-community/mathlib
Документация: https://leanprover-community.github.io/mathlib_docs/

В VSCode с помощью Ctrl + Click по названию можно удобно перейти к импортированному файлу или определению леммы/функции.

Lean поддерживает Unicode и много команд из LaTeX! Наведите курсор на символ, чтобы увидеть команду, с помощью которой его можно набрать.

Часто используемые символы:
→ = \r, \to         ← = \l              ↔ = \iff, \lr
∀ = \all, \forall   ∃ = \ex, \exists    ∈ = \in, \mem
¬ = \not, \neg      ⟨ = \<,             ⟩ = \>
≠ = \neq,           ≤ = \le             ≥ = \ge
⊆ = \ss, \sub       ⊂ = \ssub           Sᶜ = \compl, \^c
∧ = \and, \wedge    ∨ = \or, \vee       ⊢ = \goal, \|-
∩ = \cap, \inter    ∪ = \cup, \union
 -/

-- 

-- `variables (X : Type) (x : X)` позволяет в текущем контексте объявить переменные, чтобы не писать их каждый раз в сигнатурах: если вы используете `x` в определении леммы/теоремы, он автоматически добавится аргументом
-- В фигурных скобках (`{X : Type}`) записываются неявные аргументы, про них чуть позже 
variables {X : Type} (A B C : set X) (p q : X)

-- По определению, `set X` это функции из `X` в `Prop` (`X → Prop`). Если сделать Ctrl + Click по `set`, то вы перейдете к определению `set`, а там написано a ∈ X ↔ X a
-- `a ∈ X` (\in или \mem) это по определению `X a`
example : p ∈ A = A p :=
begin
  refl,
end

-- Вне tactic mode для обозначения равенства по определению используется `rfl`
example : p ∈ A = A p := rfl

-- Есть два специальных множества: `∅` (\empty) - пустое и `univ` - универсальное
-- По определению, `p ∈ ∅ = false`, `p ∈ univ = true`  
lemma mem_empty : p ∈ (∅ : set X) ↔ false :=
begin
  refl,
end

lemma mem_univ : p ∈ (set.univ : set X) ↔ true :=
begin
  refl,
end

-- `lemma` и `theorem` обычно используют для утверждений (Prop), `def` для новых определений (типов или функций)
-- Ко всему, что определено внутри namespace test, нужно обращаться с префиксом test
-- Команда #check дает проверить тип выражения (использовать внутри begin-end блока нельзя)
-- Обратите внимание на вставленные `∀ (X : Type) (A : set X) (p : X)`, которые пришли из `variables`
-- `(B C : set X)` здесь нет, потому что `B` и `C` не используются
namespace test
lemma obviously_false : p ∈ A ↔ ¬ p ∈ A := sorry
end test

#check test.obviously_false

-- `A ⊆ B` по определению то же самое, что `∀ ⦃x⦄, x ∈ A → x ∈ B` 
-- На выражение `∀ ⦃x⦄, x ∈ A → x ∈ B` следует смотреть, как на функцию, которая принимает `x` и доказательство того, что `x ∈ A`, а возвращает доказательство, что `x ∈ B` (`x` - необязательный аргумент, и можно сразу подавать `x ∈ A`)
lemma subset_def : A ⊆ B = ∀ x : X, x ∈ A → x ∈ B := rfl

lemma subset_refl : A ⊆ A :=
begin
  -- попробуйте начать сразу с `intro x`, `rw subset_def` делать не обязательно (но пока вы не знакомы с определениями, можно их раскрывать явно)
  sorry,
end

lemma subset_trans : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  sorry,
end

-- Два множества равны, если в них содержатся одинаковые элементы
-- "ext" означает extensionality, "объекты равны, если они внешне ведут себя одинаково"
-- Чтобы доказать равенство каких-то объектов (множеств, функций, ...), используйте тактику `ext`
lemma set_eq_def : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := set.ext_iff
-- A ↔ B это просто пара ⟨A → B, B → A⟩ (обратите внимание, здесь угловые скобки \< \>)

lemma subset_antisymm : A ⊆ B → B ⊆ A → A = B :=
begin
  sorry,
end

-- term mode, конструируем доказательство не тактиками, а напрямую
example : A ⊆ B → B ⊆ A → A = B := λ hAB hBA, set.ext_iff.2 (λ x, ⟨λ xA, hAB xA, λ xB, hBA xB⟩)

-- Аргументы бывают явные и неявные
-- В сигнатуре функции до `:` можно написать именованные аргументы
-- `lemma f : (h : α) : β` по сути то же самое, что `lemma f : α → β`
-- Некоторые аргументы можно делать неявными, если их можно вывести из последующих аргументов 
-- Иногда можно опустить тип аргументов (и явных, и неявных)

lemma implicit_args {X} {A B : set X} {x : X} : x ∈ A → x ∈ B := sorry
#check implicit_args
#check @implicit_args


lemma subset_trans' (X : Type) (A B C : set X) : A ⊆ B → B ⊆ C → A ⊆ C := sorry
lemma subset_trans'' {X : Type} {A B C : set X} : A ⊆ B → B ⊆ C → A ⊆ C := sorry

#check subset_trans
#check subset_trans'
#check subset_trans''
-- "@" перед названием функции делает все неявные аргументы явными
#check @subset_trans''

-- Пересечение и объединение

lemma union_def : (p ∈ A ∪ B) = (p ∈ A ∨ p ∈ B) := rfl
lemma inter_def : (p ∈ A ∩ B) = (p ∈ A ∧ p ∈ B) := rfl

-- Тактика `rcases` позволяет разбирать структуры на части за одно применение
-- Если `h : α ∧ β ∧ γ`, то `rcases h with ⟨ha, hb, hc⟩` даст три нужные гипотезы
-- Если `h : α ∨ β`, то `rcases h with (ha | hb)` даст две цели с `ha : α` в первой и `hb : β` во второй
-- Если `h : 
example : (p ∈ A ∨ p ∈ B) ∧ (p ∈ C) → p ∈ (A ∪ B) ∩ C :=
begin
  intro h,
  rcases h with ⟨(hA | hB), hC⟩,
  -- Цель: `⊢ p ∈ (A ∪ B) ∩ C`, можно с помощью `exact` и `or.inl hA` сразу сконструировать ответ
  exact ⟨or.inl hA, hC⟩,
  -- Аналогично с `or.inr hB`
  exact ⟨or.inr hB, hC⟩,   
end

-- На самом деле это верно по определению
example : (p ∈ A ∨ p ∈ B) ∧ (p ∈ C) → p ∈ (A ∪ B) ∩ C := id

-- Тактика `rintro` = `intros` + `rcases`: применяет `intros` и сразу `rcases` ко всем новым переменным
-- Когда цель выглядит как `α ∧ β → γ`, вместо того, чтобы делать `intro h`, `cases h with ha hb`, можно использовать `rintro ⟨hA, hB⟩` и сразу получить `hA : α`, `hB : β` в контексте
example : p ∈ A ∨ (p ∈ B ∧ p ∈ C) → p ∈ A ∪ (B ∩ C) :=
begin
  rintro (pA | ⟨pB, pC⟩),
  -- две цели, соответствующие двум конструкторам `or`
  left, exact pA,
  right, exact ⟨pB, pC⟩,
end

lemma inter_assoc (A B C : set X) : (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
begin
  sorry,
end 

lemma union_assoc (A B C : set X) : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
begin
  sorry,
end

-- Тактика `all_goals {...}` применяет блок ко всем целям
example (A B C : set X) : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
begin
  ext x, split,
  all_goals {repeat {rw set.mem_union}, tauto},
end

lemma union_eq_of_subset (hAB : A ⊆ B) : A ∪ B = B :=
begin
  sorry,
end

lemma inter_eq_iff_subset : A ⊆ B ↔ A ∩ B = A :=
begin
  sorry,
end

-- `Aᶜ` (A\^c) это дополнение `A`, то есть, `p ∈ Aᶜ = p ∉ A = ¬p ∈ A`
#check @set.mem_compl
example : p ∉ A  = ¬p ∈ A := rfl
example : p ∈ Aᶜ = (p ∉ A) := rfl

lemma compl_subset_compl_of_subset (hAB : A ⊆ B) : Bᶜ ⊆ Aᶜ :=
begin
  sorry,
end

-- Закон де Моргана
-- Полезные тактики: `simp at h ⊢` упростит локальную гипотезу и цель (можно также написать `simp at *`, что будет упрощать все локальные гипотезы и цель)
-- `tauto` решает цели в логике высказываний, `tauto!` работает в классической логике и может использовать закон исключенного третьего
lemma compl_inter_eq_compl_union_compl : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ :=
begin
  sorry,
end

-- Для объединения/пересечений нескольких множеств есть следующие операторы:
-- Леммы про них лежат в `data.set.lattice`
-- 1. Если `f : ι → set S`, то `⋃ (i : ι), f i` равно объединению `f i`, где `i` пробегает все элементы типа `ι`
-- `x` принадлежит `⋃ (i : ι), f i` ↔ `∃ i, x ∈ f i`
-- Леммы про такое объединение содержат `Union` в названии 

lemma Union_def {S ι} {F : ι → set S} : set.Union F = ⋃ i, F i :=
begin
  refl,
end 

lemma mem_Union {S ι} {x : S} {F : ι → set S} : (x ∈ ⋃ i, F i) ↔ (∃ i, x ∈ F i) := 
begin
  exact set.mem_Union,
end

-- 2. `bUnion` (от bounded union) берет объединение только по `i`, лежащим в множестве `I : set ι`
-- Обратите внимание на нотацию `∃ i ∈ I`, это сокращение от `∃ i (H : i ∈ I)`, то есть, "существует `i` и доказательство `i ∈ I`"
lemma mem_bUnion {S ι} {x : S} {F : ι → set S} {I : set ι} : (x ∈ ⋃ i ∈ I, F i) ↔ (∃ i ∈ I, x ∈ F i) := 
begin
  exact set.mem_bUnion_iff,
end

-- 3. Если у нас есть (s : set (set S)), то `⋃₀ s : set S` объединяет все множества, лежащие в `s`
-- Леммы про такое объединение содержат `sUnion` в названии 
lemma mem_sUnion {S} {x : S} {s : set (set S)} : (x ∈ ⋃₀ s) ↔ (∃ t ∈ s, x ∈ t) := 
begin
  exact set.mem_sUnion, 
end

-- Пересечение всех множеств, содержащих `S` как подмножество, равно `S`
def supersets {X : Type} (S : set X) : set (set X) := {T | S ⊆ T} 

lemma supersets_sInter {S : set X} : ⋂₀ (supersets S) = S :=
begin
  sorry,
end  