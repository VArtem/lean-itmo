import tactic

-- Этот файл переведен и адаптирован из второй недели курса Formalising Mathematics: https://github.com/ImperialCollegeLondon/formalising-mathematics/tree/master/src/week_2
-- Там же есть продолжение про подгруппы, скачайте репозиторий с помощью
-- `leanproject get ImperialCollegeLondon/formalising-mathematics`
-- И самостоятельно пройдите то, что там есть 

namespace itmo.lean

/-
Определим группу как тайпкласс (подробнее: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html), расширяющий `has_mul`, `has_one` и `has_inv`. 

`has_mul G` означает, что на `G` определено умножение `* : G → G → G`
`has_one G` означает, что в `G` есть единица `1 : G`
`has_inv G` означает, что есть функция, выдающая обратный для элемента `G`: `⁻¹ : G → G`

Все эти определения - просто нотация, свойства и взаимодействие этих функций надо будет добавить. Определим класс `group` с аксиомами групп:
-/

class group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

/-
Формально, `group G` это структура, в которой есть умножение, 1, обратный элемент, и доказательства аксиом групп. Поскольку `group G` это тайпкласс, то добавить в сигнатуру функции "пусть `G` - группа" нужно, как `(G : Type) [group G]`. Квадратные скобки используются для тайпклассов и автоматически (насколько получится) находятся соответствующие инстансы для `G`.

Обратите внимание, что набор использованных аксиом минимален, например, нет аксиом 
`mul_one : ∀ (a : G), a * 1 = a` и 
`mul_right_inv : ∀ (a : G), a * a⁻¹ = 1`.

На самом деле, эти аксиомы следуют из основных, и мы это докажем.
-/

namespace group

variables {G : Type} [group G]

lemma mul_left_cancel (a b c : G) (Habac : a * b = a * c) : b = c := 
begin
  sorry,
end

-- Доказательства из длинных цепочек равенств или неравенств часто можно заменить на `calc` (справка по `calc`: https://leanprover-community.github.io/extras/calc.html)
-- Пример решения задачи с IMO 2020 с использованием `calc`: https://github.com/leanprover-community/mathlib/blob/master/archive/imo/imo2020_q2.lean

example (a b c : G) (Habac : a * b = a * c) : b = c := 
begin
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw ← mul_left_inv a
    ... = a⁻¹ * (a * b) : by rw ← mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw ← mul_assoc
    ... = 1 * c         : by rw mul_left_inv a
    ... = c             : by rw one_mul,
end

lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  sorry,
end

variables (a b c x y : G)

/-
Попробуйте начать доказательство с `apply mul_eq_of_eq_inv_mul`.
-/

@[simp] theorem mul_one : a * 1 = a :=
begin
  sorry,
end

@[simp] theorem mul_right_inv : a * a⁻¹ = 1 :=
begin
  sorry,
end


/-

Хорошей идеей было бы научить `simp` работать с леммами вида `A = B` или `A ↔ B`, которые мы описали выше. Для этого мы написали атрибут `@[simp]` перед леммой. В идеале, хочется, чтобы равенства в группах решались автоматически:

`example : (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1`

Тактика `simp` будет пытаться "упростить" цель как можно больше, в идеале закрыть цель с помощью известных ей лемм. `simp` работает переписываниями, только используя переписывания слева направо (если хочется изменить направление, можно дать дополнительный аргумент `simp [← h] at ...`). Поэтому, в тождествах, помеченных `simp`, правая часть должна быть "проще", чем левая. В частности, `add_comm (a b : ℕ) : a + b = b + a` - плохая лемма для `simp`. Обратите внимание, что во всех леммах выше, например,

`@[simp] theorem mul_one (a : G) : a * 1 = a`
`@[simp] theorem mul_right_inv (a : G) : a * a⁻¹ = 1`

правая часть проще левой. Помечать равенство  `a = a * 1` тегом `@[simp]` - плохая идея.

Уже определенным функциям (или определенным в другом файле) можно ретроспективно проставить атрибуты вручную.
-/

attribute [simp] one_mul mul_left_inv mul_assoc

/-
Научим `simp` использовать следующие пять лемм: 

`inv_mul_cancel_left : a⁻¹ * (a * b) = b`
`mul_inv_cancel_left : a * (a⁻¹ * b) = b`
`inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹`
`one_inv : (1 : G)⁻¹ = 1`
`inv_inv : (a⁻¹)⁻¹ = a`

Обратите внимание, что везде правая часть "проще" левой.
-/

@[simp] lemma inv_mul_cancel_left : a⁻¹ * (a * b) = b :=
begin
  rw ← mul_assoc,
  -- Здесь уже `simp` сможет переписать `a⁻¹ * a = 1` и `1 * b = b`
  simp,
end

@[simp] lemma mul_inv_cancel_left : a * (a⁻¹ * b) = b :=
begin
  sorry,
end

@[simp] lemma inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  sorry,
end

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  sorry,
end

@[simp] lemma inv_inv : a ⁻¹ ⁻¹ = a :=
begin
  sorry,
end

/-
Эти 5 лемм выбраны неспроста: это вывод алгоритма Кнута-Бендикса для переписываний в группе:

https://en.wikipedia.org/wiki/Word_problem_(mathematics)#Example:_A_term_rewriting_system_to_decide_the_word_problem_in_the_free_group
-/

-- Сложный пример теперь решается автоматически
example : (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by simp

lemma eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
begin
  sorry,
end

lemma eq_inv_mul_of_mul_eq {a b c : G} (h : b * a = c) : a = b⁻¹ * c :=
begin
  sorry,
end

lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 :=
begin
  sorry,
end

lemma mul_right_eq_self {a b : G} : a * b = a ↔ b = 1 :=
begin
  sorry,
end

lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
calc  a = a * 1 : by rw mul_one
    ... = b⁻¹   : by sorry

lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
begin
  sorry,
end

lemma unique_left_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 :=
begin
  sorry,
end

lemma unique_right_inv {a b : G} (h : a * b = 1) : b = a⁻¹ :=
begin
  sorry,
end

lemma mul_left_cancel_iff (a x y : G) : a * x = a * y ↔ x = y :=
begin
  sorry,
end

lemma mul_right_cancel (a x y : G) (Habac : x * a = y * a) : x = y := 
calc x = x * 1 : by rw mul_one
  ... = y : by sorry

@[simp] theorem inv_inj_iff {a b : G}: a⁻¹ = b⁻¹ ↔ a = b :=
begin
  sorry,
end   

theorem inv_eq {a b : G}: a⁻¹ = b ↔ b⁻¹ = a :=
begin
  sorry,
end  

end group

end itmo.lean

