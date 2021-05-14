import tactic

-- Этот файл переведен и адаптирован из второй недели курса Formalising Mathematics: https://github.com/ImperialCollegeLondon/formalising-mathematics/tree/master/src/week_2


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
  rw ← one_mul b,
  rw ← one_mul c,
  rw ← mul_left_inv a,
  rw mul_assoc,
  rw mul_assoc,
  rw Habac,
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
  apply mul_left_cancel,
  rwa [← mul_assoc, mul_left_inv, one_mul],
end

variables (a b c x y : G)

/-
Попробуйте начать доказательство с `apply mul_eq_of_eq_inv_mul`.
-/

@[simp] theorem mul_one : a * 1 = a :=
begin
  exact mul_eq_of_eq_inv_mul (mul_left_inv _).symm, 
end

@[simp] theorem mul_right_inv : a * a⁻¹ = 1 :=
begin
  exact mul_eq_of_eq_inv_mul (mul_one _).symm,
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
  rw [← mul_assoc],
  simp,
end

@[simp] lemma inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv,
  simp,
end

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  apply mul_left_cancel (1 : G),
  rw mul_right_inv,
  simp,
end

@[simp] lemma inv_inv : a ⁻¹ ⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  simp,
end

/-
Эти 5 лемм выбраны неспроста: это вывод алгоритма Кнута-Бендикса для переписываний в группе:

https://en.wikipedia.org/wiki/Word_problem_(mathematics)#Example:_A_term_rewriting_system_to_decide_the_word_problem_in_the_free_group
-/

-- Сложный пример теперь решается автоматически
example : (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by simp

lemma eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
begin
  rw ← h,
  simp,
end

lemma eq_inv_mul_of_mul_eq {a b c : G} (h : b * a = c) : a = b⁻¹ * c :=
begin
  rw ← h,
  simp,
end

lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 :=
begin
  split, {
    intro h,
    replace h := congr_arg (λ x, x * b⁻¹) h,
    simpa using h,
  }, {
    intro h,
    simp [h],
  }
end

lemma mul_right_eq_self {a b : G} : a * b = a ↔ b = 1 :=
begin
  split, {
    intro h,
    replace h := congr_arg (λ x, a⁻¹ * x) h,
    simp at h,
    exact h,
  }, {
    intro h,
    simp [h],
  }
end

lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
calc  a = a * 1 : by rw mul_one
    ... = a * (b * b⁻¹) : by rw mul_right_inv
    ... = (a * b) * b⁻¹ : by rw mul_assoc
    ... = 1 * b⁻¹ : by rw h
    ... = b⁻¹   : one_mul _

lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
begin
  replace h := eq_inv_of_mul_eq_one h,
  simp [h],
end

lemma unique_left_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 :=
begin
  have h1 := h 1,
  simpa using h1,
end

lemma unique_right_inv {a b : G} (h : a * b = 1) : b = a⁻¹ :=
begin
  apply mul_left_cancel a,
  simp [h],
end

lemma mul_left_cancel_iff (a x y : G) : a * x = a * y ↔ x = y :=
begin
  split,
  { apply mul_left_cancel },
  { intro hxy,
    rwa hxy }
end

-- В режим `calc` можно войти даже вне блока begin-end 
lemma mul_right_cancel (a x y : G) (Habac : x * a = y * a) : x = y := 
calc x = x * 1 : by rw mul_one
  ... = x * (a * a⁻¹) : by rw ← mul_right_inv
  ... = (x * a) * a⁻¹ : by rw ← mul_assoc
  ... = (y * a) * a⁻¹ : by rw Habac
  ... = y * (a * a⁻¹) : by rw mul_assoc
  ... = y * 1 : by rw mul_right_inv
  ... = y : by rw mul_one

@[simp] theorem inv_inj_iff {a b : G}: a⁻¹ = b⁻¹ ↔ a = b :=
begin
  split, {
    intro h,
    rw [← inv_inv a, h, inv_inv],
  }, {
    rintro rfl,
    refl,
  }
end   

theorem inv_eq {a b : G}: a⁻¹ = b ↔ b⁻¹ = a :=
begin
  split, 
  all_goals {
    rintro rfl,
    simp only [inv_inv],
  },
end  

end group

end itmo.lean

