import data.real.basic
import tactic

/-

-- Этот файл переведен и адаптирован из третьей недели курса Formalising Mathematics: https://github.com/ImperialCollegeLondon/formalising-mathematics/blob/master/src/week_3/Part_A_limits.lean

В этом файле мы разовьем теорию пределов последовательностей вещественных чисел через привычное определение предела. Последовательность `a₀, a₁, ...` будем моделировать, как функцию `ℕ → ℝ`

Определим отношение `is_limit (a : ℕ → ℝ) (l : ℝ)`, означающее, что  `aₙ → l`:

`∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε`

Теоремы в этом файле:

* `variables (a b c : ℕ → ℝ) (c l m : ℝ)`
* `is_limit_const : is_limit (λ n, c) c`
* `is_limit_subsingleton (hl : is_limit a l) (hm : is_limit a m) : l = m`
* `is_limit_add (h1 : is_limit a l) (h2 : is_limit b m) : is_limit (a + b) (l + m)`
* `is_limit_mul (h1 : is_limit a l) (h2 : is_limit b m) : is_limit (a * b) (l * m)`
* `is_limit_le_of_le (hl : is_limit a l) (hm : is_limit b m) (hle : ∀ n, a n ≤ b n) : l ≤ m`
* `sandwich (ha : is_limit a l) (hc : is_limit c l)`
    `(hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l`

-/


variable asd : ℝ

local notation `|` x `|` := abs x

definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

/-
Обратите внимание, что предел последовательности это не функция `(ℕ → ℝ) → ℝ`, а бинарное отношение над (ℕ → ℝ) и ℝ, потому что у некоторых последовательностей нет пределов, и в теории, некоторые последовательности могут иметь несколько пределах (в определенных пространствах).
-/

/-- Предел константной последовательности - константа -/
lemma is_limit_const (c : ℝ) : is_limit (λ n, c) c :=
begin
  -- `is_limit a l` по определению это `∀ ε, ε > 0 → ...`, поэтому сразу начинаем с `intros`.
  intros ε εpos,
  -- Нужно предъявить `N`, начиная с которого выполняется неравенство, подойдет любое
  use 37,
  -- Теперь берем любое `n ≥ N` и докажем про это конкретное `n` неравенство
  -- Второй параметр бесполезен, поэтому можно написать `-`, тогда в нашем контексте его не будет
  rintro n -,
  -- В цели у нас есть `(λ (n : ℕ), c) n` - нередуцированная лямбда
  -- Чтобы избавиться от таких (и подобных неудобств), используем `dsimp only`
  dsimp only,
  -- `simp` должен знать о том, что `c - c = 0` и `abs 0 = 0`
  simp,
  -- `a > b` по определению равно `b < a` поэтому сработает `exact`
  exact εpos,
end

theorem is_limit_subsingleton {a : ℕ → ℝ} {l m : ℝ} (hl : is_limit a l)
(hm : is_limit a m) : l = m :=
begin
  -- Докажем от противного: пусть l ≠ m
  by_contra h,

  -- Идея математического доказательства:  возьмем `ε = |l - m| / 2`
  -- Тогда последовательность `a` будет в пределах `ε` от `l` и в пределах `ε` от `m`
  -- Из чего мы получим противоречие
  
  -- Чтобы уменьшить количество случаев тогда, когда цель и все локальные гипотезы симметричны,
  -- Используем тактику `wlog`: https://leanprover-community.github.io/mathlib_docs/tactic/wlog.html

  wlog hlm : l < m,
  -- Lean проверит симметричность относительно `l` и `m`
  -- Но сгенерирует новую цель `l < m` or `m < l`
  { have : l < m ∨ l = m ∨ m < l := lt_trichotomy l m,
  -- Осталась чисто логическая цель: ¬ B, A ∨ B ∨ C ⊢ A ∨ C, `tauto` справится
    tauto },

  -- Возьмем `ε = (m - l) / 2`, обозначим за `hε` определение `e` 
  set ε := (m - l)/2 with hε,
  -- Докажем, что `ε > 0`, тактика `linarith` справится
  have εpos : ε > 0 := by linarith,
  
  -- Подставим это `ε`, а также доказательство, что `ε > 0` в определение предела `hl` и `hm`
  specialize hl ε εpos,
  specialize hm ε εpos,

  -- Теперь `hl` и `hm` выглядят, как ∃ N, ∀ n ≥ m, |a n - l| < ε, разберем их на части
  cases hl with L hL,
  cases hm with M hM,
  
  -- Определим `N = max L M`,
  set N := max L M with hN,
  have hLN : L ≤ N := le_max_left L M,
  have hMN : M ≤ N := le_max_right L M,
  
  -- Подставим `N` в локальные утверждения `hL` и `hM`, вместе с доказательствами, что `N ≥ L` и `N ≥ M` 
  specialize hL N hLN,
  specialize hM N hMN,

  -- У нас есть утверждения `hL: |a N - l| < ε`, `hM: |a N - m| < ε` и `hε: ε = (m - l) / 2`
  -- Хочется решить их автоматически, тактика `linarith` заточена на то, чтобы решать линейные неравенства
  -- Но `linarith` не знает про `abs`, поэтому надо помочь
  rw abs_lt at hL hM,
  linarith,
end


/-
Поподробнее про тактики `linarith`, `ring` и `convert`

### `ring`

Тактика `ring` доказывает цели в коммутативных кольцах (или даже
в коммутативных полукольцах типа ℕ). Например, если `(x y : ℝ)` 
и цель равна `(x+y)^3=x^3+3*x^2*y+3*x*y^2+y^3`, то `ring` справится
закрыть эту цель.
В следующем доказательстве `is_limit_add` полезно использовать `ring`, чтобы доказать
равенства вида `a n + b n - (l + m) = (a n - l) + (b n - m)` и `ε/2 + ε/2 = ε`.
К сожалению, `ring` не понимает `λ`-термы и работает с точностью до синтаксического равенства.
Также, `ring` работает только с целью, не смотря на локальные гипотезы, поэтому в примере
```
a b c : ℝ 
ha : a = b + c
⊢ 2 * a = b + b + c + c
```
Просто `ring` не сработает, сначала нужно сделать `rw ha`.

### `linarith`

`linarith` решает линейные уравнения, например:

```
a b c : ℝ 
hab : a ≤ b
hbc : b < c
⊢ a ≤ c + 1
```

`linarith` смотрит только на гипотезы, являющиеся неравенствами, и не сможет решить следующий пример:

```
a b c : ℝ 
hab : a ≤ b
hbc : a ≤ b → b < c
⊢ a ≤ c + 1
```

Кроме одного случая: если в гипотезе есть `∧`, то `linarith` сможет использовать оба аргумента

```
a b c : ℝ 
h : a ≤ b ∧ b < c
⊢ a ≤ c + 1
```

Но не сможет доказать `∧` в цели, нужно сделать `split`

```
a b c : ℝ 
h : a ≤ b ∧ b < c
⊢ a ≤ c + 1 ∧ a ≤ c + 1
```

### convert

Тактика `convert` позволяет заменить цель на слегка отличающуюся, и оставляет
цели в местах отличия целей. Если цель `⊢ P` и есть гипотеза `h : P'`, где `P` и `P'`
отличаются несильно, то `convert h'` закроет цель и создает несколько целей для всех мест, где `P` и `P` отличаются. 

Например:
-/

example (a b : ℝ) (h : a * 2 = b + 1) : a + a = b - (-1) :=
begin
  -- `rw h` не сработает, потому что `a * 2` нигде не встречается
  convert h,
  -- Сгенерировано две цели: `a + a = a * 2` и `b - -1 = b + 1`
  { ring },
  { ring },
end

/-
Иногда `convert` уходит слишком глубоко, и ему придется ограничить глубину сравнения.
Попробуйте раскомментировать `convert h` ниже, и посмотрите, какие цели получились. 
-/
example (a b : ℝ) (h : a * 2 = b + 1) : a + a = 1 + b :=
begin
  -- convert h,
  convert h using 1, -- если заменить на `using 2` или больше, будет тот же эффект
  { ring },
  { ring }
end


lemma is_limit_add_const {a : ℕ → ℝ} {l : ℝ} (c : ℝ) (ha : is_limit a l) :
  is_limit (λ i, a i + c) (l + c) :=
begin
  sorry,
end

lemma is_limit_add_const_iff {a : ℕ → ℝ} {l : ℝ} (c : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i + c) (l + c) :=
begin
  sorry,
end

lemma is_limit_iff_is_limit_sub_eq_zero (a : ℕ → ℝ) (l : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i - l) 0 :=
begin
  sorry,
end

/-

Докажем, что если aₙ → l и bₙ → m то aₙ + bₙ → l + m.

Математическое рассуждение, возьмем ε/2, 
Выберем достаточно большое L, чтобы из n ≥ L следовало |aₙ - l| < ε/2
Выберем достаточно большое M, чтобы из n ≥ M следовало |bₙ - m| < ε/2
Теперь N = max L M сработает.
Полезные леммы:
`pi.add_apply a b : (a + b) n = a n + b n` и другие начинающиеся с `pi.`
`abs_add x y : |x + y| ≤ |x| + |y|`
Удачи!
-/

theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  sorry,
end

-- Также докажем про взаимодействие предела и умножения
-- Полезные леммы
-- `abs_pos : 0 < |a| ↔ a ≠ 0`
-- `div_pos : 0 < a → 0 < b → 0 < a / b`
-- `abs_mul x y : |x * y| = |x| * |y|`
-- `lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b)`
-- Эти и похожие полезные леммы можно найти либо "угадая" название леммы
-- В комбинации с ctrl+пробел, или `library_search`

-- Докажем, что с * aₙ → c * l
-- Скорее всего, c = 0 будет отдельным случаем, поэтому начните с 
-- `by_cases hc : c = 0`

lemma is_limit_mul_const_left {a : ℕ → ℝ} {l c : ℝ} (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) :=
begin
  sorry, 
end

lemma is_limit_linear (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + d * (b n) ) (c * α + d * β) :=
begin
  sorry,
end


-- Перейдем к пределу произведения
-- Вместо использования `√ε`, выберите `N` так, чтобы `|a n| ≤ ε`
-- и `|b n| ≤ 1`, когда `n ≥ N`; этого достаточно.

lemma is_limit_mul_eq_zero_of_is_limit_eq_zero {a : ℕ → ℝ} {b : ℕ → ℝ}
  (ha : is_limit a 0) (hb : is_limit b 0) : is_limit (a * b) 0 :=
begin
  sorry,
end


-- Если aₙ → l и bₙ → m то aₙ * bₙ → l * m.
-- Рекомендуемое доказательство: начните с 
-- `suffices : is_limit (λ i, (a i - l) * (b i - m) + (l * (b i - m)) + m * (a i - l)) 0,`
-- (выражение внутри равно `a i * b i - l * m`)
-- разложите на сумму трех слагаемых, показав, что предел каждого равен 0
theorem is_limit_mul (a : ℕ → ℝ) (b : ℕ → ℝ) (l m : ℝ)
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  suffices : is_limit (λ i, (a i - l) * (b i - m) + (l * (b i - m)) + m * (a i - l)) 0,
  { sorry, },
  sorry,
end


-- Если aₙ → l и bₙ → m, а также aₙ ≤ bₙ для всех n, то l ≤ m
theorem is_limit_le_of_le (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m) 
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  sorry,
end

-- Полицейские сэндвичи
theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  sorry,
end

-- Определение ограниченной последовательности
definition is_bounded (a : ℕ → ℝ) := ∃ B, ∀ n, |a n| ≤ B

-- Произведение бесконечно малой на ограниченную
lemma tendsto_bounded_mul_zero {a : ℕ → ℝ} {b : ℕ → ℝ}
  (hA : is_bounded a) (hB : is_limit b 0) 
  : is_limit (a*b) 0 :=
begin
  sorry,
end

-- Можно продолжить определять новые понятия, и так далее, ...
def is_cauchy (a : ℕ → ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε 

