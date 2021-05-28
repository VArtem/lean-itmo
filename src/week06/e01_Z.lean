import tactic

-- Основано на https://github.com/ImperialCollegeLondon/formalising-mathematics/tree/master/src/week_7
-- Я убрал довольно много материала оттуда, посмотрите по возможности оригинал, в котором Kevin уходит гораздо глубже в концепцию `quotient`
-- Больше в книге Theorem Proving in Lean: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients

-- В этом файле мы изучим конструкцию `quotient`
-- И построим целые числа как классы эквивалентности пар натуральных чисел (a, b)
-- Где (a, b) ≈ (c, d) ↔ a + d = b + c
-- В первом приближении `quotient` можно описать как "тип классов эквивалентности по бинарному отношению"
-- Пусть у нас есть тип `α` и отношение эквивалентности `r : α → α → Prop`

-- `abbreviation` это просто синтаксический синоним
abbreviation N2 := ℕ × ℕ

namespace N2

section product

def foo : ℕ × ℕ := (3, 4)

#reduce (foo.fst, foo.snd)
-- Аналогично можно писать `foo.1` или `foo.2`

-- Чтобы доказать равенство двух пар, можно использовать `ext` 
example (X Y : Type) (s t : X × Y) (h1 : s.fst = t.fst) (h2 : s.snd = t.snd) :
  s = t :=
begin
  ext,
  { exact h1 },
  { exact h2 },
end

-- Чтобы разбить пару `x` на два натуральных числа, можно использовать `cases x with a b`
example (A B : Type) (x : A × B) : x = (x.1, x.2) :=
begin
  cases x with a b,
  -- ⊢ (a, b) = ((a, b).fst, (a, b).snd)
  dsimp only, -- упрощает `(a, b).fst` до `a`.
  -- ⊢ (a, b) = (a, b)
  refl,
end

end product

-- Как построить целые числа на основе натуральных? 
-- Стандартная конструкция: целое число либо `n : ℕ`, либо `-n-1`
#check ℤ

-- Иначе целые числа можно представить, как разность двух натуральных чисел, например, -1 = 3 - 4
-- Такое представление неоднозначно, 3 - 4 = 5 - 6 = ...
-- В каком случае две пары задают одно число? a - b = c - d ↔ a + d = c + b
-- Определим отношение `r : N2 → N2 → Prop`: r (a, b) (c, d) = a + d = c + b

def r (ab cd : N2) : Prop :=
ab.1 + cd.2 = cd.1 + ab.2

lemma r_def (ab cd : N2) : r ab cd ↔ ab.1 + cd.2 = cd.1 + ab.2 := iff.rfl

lemma r_def' (a b c d : ℕ) : r (a,b) (c,d) ↔ a + d = c + b := iff.rfl

def r_refl : reflexive r :=
begin
  -- `unfold reflexive` раскроет определение и покажет, как оно определено
  -- не забывайте, что N2 = ℕ × ℕ, поэтому можно делать `rintro ⟨a, b⟩`
  sorry,
end
 
def r_symm : symmetric r :=
begin
  sorry,
end

def r_trans : transitive r :=
begin
  sorry,
end

-- Определим инстанс класса `setoid`: это просто отношение эквивалентности на `N2`
instance setoid : setoid N2 := ⟨r, r_refl, r_symm, r_trans⟩

-- Теперь можно использовать `≈` (\~~ или \approx) 

example (x y : N2) : x ≈ y ↔ r x y := iff.rfl

-- Добавим simp-леммы для упрощения жизни в будущем
@[simp] lemma equiv_def (ab cd : N2) : ab ≈ cd ↔ ab.1 + cd.2 = cd.1 + ab.2 :=
begin
  refl
end

@[simp] lemma equiv_def' (a b c d : ℕ) : (a,b) ≈ (c,d) ↔ a + d = c + b := iff.rfl 

end N2

open N2

-- Определим Z как `quotient` по определенному отношению эквивалентности
def Z := quotient N2.setoid

namespace Z

-- По заданной паре типа N2 можно легко получить элемент типа Z как `quotient.mk x`
-- Или же `⟦x⟧`

def bar : Z := quotient.mk foo -- соответствует целому числу -1.

example : bar = ⟦foo⟧ := rfl

-- Посмотрим на API `quotient`

example (x y : N2) : x ≈ y → ⟦x⟧ = ⟦y⟧ := quotient.sound

example (x y : N2) : ⟦x⟧ = ⟦y⟧ → x ≈ y := quotient.exact

example (x y : N2) : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y := quotient.eq

-- Определим и докажем все операции над Z, дойдя до коммутативного кольца

-- Определим 0 и 1:

def zero : Z := ⟦(0, 0)⟧

def one : Z := ⟦(1, 0)⟧

instance : has_zero Z := ⟨zero⟩
instance : has_one Z := ⟨one⟩

@[simp] lemma zero_def : (0 : Z) = ⟦(0, 0)⟧ := rfl  
@[simp] lemma one_def : (1 : Z) = ⟦(1, 0)⟧ := rfl

/-
Определим обратное по сложению число. Как определить функцию для `quotient`?

1) Определим вспомогательное отображение `N2 → Z`: по `(a,b)` выдаем `⟦(b,a)⟧`
2) Докажем, что эта функция константна на классах эквивалентности:
  `(a, b) ≈ (c, d) → ⟦(b, a)⟧ = ⟦(d, c)⟧`
3) Используем `quotient.lift`, чтобы получить функцию `Z → Z`.

-/

def neg_aux (ab : N2) : Z := ⟦(ab.2, ab.1)⟧

@[simp] lemma neg_aux_def (ab : N2) : neg_aux ab = ⟦(ab.2, ab.1)⟧ := rfl

def neg : Z → Z := quotient.lift neg_aux 
begin
  -- ⊢ ∀ (a b : N2), a ≈ b → neg_aux a = neg_aux b
  intros a b rab,
  sorry,
end

-- нотация `-z`
instance : has_neg Z := ⟨neg⟩

@[simp] lemma neg_def (a b : ℕ) : (-⟦(a, b)⟧ : Z) = ⟦(b, a)⟧ := rfl

/-
Определим сложение. Если бы мы определяли сложение так же, как отрицание, то пришлось бы использовать
`lift` дважды: сначала показать, что функция независима по первому аргументу, потом по второму.
Есть функция `quotient.lift₂`, которая позволяет взять функцию `f : A → B → C`,
и доказательство, что она не меняет значение, если заменить первые два аргумента на эквивалентные, и выдает функцию `A/~ → B/~ → C`.
-/

-- Вспомогательное определение сложения (note `(a-b)+(c-d)=(a+c)-(b+d)` )
def add_aux (ab cd : N2) : Z := ⟦(ab.1 + cd.1, ab.2 + cd.2)⟧

-- И simp-лемма для него
@[simp] lemma add_aux_def (ab cd : N2) : add_aux ab cd = ⟦(ab.1 + cd.1, ab.2 + cd.2)⟧ := rfl 

def add : Z → Z → Z := quotient.lift₂ add_aux 
begin
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ rab rcd,
  sorry,
end

instance : has_add Z := ⟨add⟩

@[simp] lemma add_def (a b c d : ℕ) :
  (⟦(a, b)⟧ + ⟦(c, d)⟧ : Z) = ⟦(a+c, b+d)⟧ := 
rfl

-- И определим вычитание целых чисел
def sub (x y : Z) : Z := x + -y

instance : has_sub Z := ⟨sub⟩

-- Покажем, что Z - коммутативная группа по сложению

def add_comm_group : add_comm_group Z :=
{ zero := 0,
  add := (+),
  neg := has_neg.neg, 
  sub := has_sub.sub,
  -- Используйте `quotient.induction_on` для доказательства лемм про свойства операций над `quotient`
  -- "Если для всех `x : N2` верно `p ⟦x⟧`, то для всех `y : Z` верно p y"
  zero_add := begin
    intro x,
    apply quotient.induction_on x, clear x,
    rintro ⟨a, b⟩,
    simp,
  end,
  add_zero := begin
    sorry,
  end,    
  -- Для версий с 2 и 3 аргументами есть `quotient.induction_on₂` и `quotient.induction_on₃`
  -- Не забывайте про `linarith` и `ring`
  add_assoc := begin
    sorry,
  end,
  add_left_neg := begin
    sorry,
  end,
  add_comm := begin
    sorry,
  end,
}

-- Умножение: `(a-b)*(c-d) = (a*c+b*d)-(a*d+b*c)`
def mul_aux (ab cd : N2) : N2 :=
  (ab.1 * cd.1 + ab.2 * cd.2, ab.1 * cd.2 + ab.2 * cd.1)

@[simp] lemma mul_aux_def (a b c d : ℕ) :
  mul_aux (a,b) (c,d) = (a*c+b*d,a*d+b*c) := rfl

-- Для разнообразия определим умножение слегка иначе.
-- Вместо использования `quotient.lift₂` (который превращает `N2 → N2 → Z` в `Z → Z → Z`),
-- используем `quotient.map₂`, который превращает `N2 → N2 → N2` в `Z → Z → Z`.
-- `nlinarith` умеет доказывать некоторые цели, содержащие нелинейные [не]равенства
def mul : Z → Z → Z := quotient.map₂ mul_aux 
begin
  sorry,
end

instance : has_mul Z := ⟨mul⟩

@[simp] lemma mul_def (a b c d : ℕ) :
  (⟦(a, b)⟧ * ⟦(c, d)⟧ : Z) = ⟦(a*c+b*d, a*d+b*c)⟧ := rfl

-- И наконец, докажем, что Z - коммутативное кольцо
def comm_ring : comm_ring Z :=
{ one := 1,
  add := (+),
  mul := (*),
  mul_assoc := begin
    sorry,
  end,
  one_mul := begin
    sorry,
  end,
  mul_one := begin
    sorry,
  end,
  left_distrib := begin
    sorry,
  end,
  right_distrib := begin
    sorry,
  end,
  mul_comm := begin
    sorry,
  end,
  ..add_comm_group
}

end Z
