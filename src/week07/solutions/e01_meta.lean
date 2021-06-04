import tactic
import data.equiv.list

-- Упражнения на метапрограммирование адаптированы из видеокурса конференции lftcm2020
-- https://www.youtube.com/watch?v=o6oUjcE6Nz4&list=PLlF-CfQhukNlxexiNJErGJd2dte_J1t1N&index=19

-- Все вычисления, что мы раньше рассматривали в Lean, обязательно должны завершаться

def f : ℕ → ℕ
| 0 := 0
| (n + 1) := have (n + 1) / 2 < (n + 1), from nat.div_lt_self' n 0, 
             f ((n + 1) / 2) + 1

-- Для всех определений Lean должен понять (возможно, с нашей помощью), что
-- вычисления всегда гарантированно завершаются 
-- Более точно, нужно показать, что рекурсия well-founded: https://leanprover-community.github.io/extras/well_founded_recursion.html

-- Это означает, что написать функцию, вычисляющую последовательность Коллатца нельзя:

-- def c : ℕ → ℕ
-- | n := if (n = 1) then 1
-- else if (n % 2 = 0) then c (n / 2)
-- else c ((3 * n + 1) / 2)

-- #reduce работает в проверенном "простом" ядре Lean, все вычисления надежны (насколько возможны), но очень медленные и непригодные для вычисления

#reduce (show 2 ≤ 10, from dec_trivial)

-- Stack overflow:
-- #reduce 123 * 345

-- Даже такое вызовет deterministic timeout
-- #reduce [1, 0].merge_sort (≤)


-- Специальное ключевое слово `meta`, которое по сути отключает termination checker + переключает Lean из режима trusted core в режим VM
-- Вычисления в VM стоит рассматривать как небезопасные 

meta def c2 : ℕ → list ℕ
| n := n :: (if (n = 1) then []
else if (n % 2 = 0) then c2 (n / 2)
else c2 ((3 * n + 1) / 2))

-- Если `c2` объявлено как `meta`, то все, что использует `c2`, тоже должно быть `meta`

-- def d := c2
-- invalid definition, it uses untrusted declaration 'c2'

-- Для вычисления meta определений можно использовать #eval
#eval c2 123
#eval 123456789 * 987654321

-- Докательство `false` методом бесконечной рекурсии
meta def inf_false : false := 
begin
  -- в контексте есть `inf_false`!
  exact inf_false
end

-- Тактики работают на meta-уровне, могут зависать, фейлиться, либо использовать неограниченный перебор

-- 1. Построение терма напрямую
example {A B : Prop} : A ∧ B → B ∧ A := λ ab, and.elim ab (λ a b, and.intro b a)

-- 2. Использование тактик для построения термов
example {A B : Prop} : A ∧ B → B ∧ A :=
begin
  intro ab,
  cases ab with a b,
  split,
  exact b,
  exact a,
end

-- 3. Программирование тактик - ???
-- Написание тактик - классический пример монадического программирования
-- `tactic` - state монада с состоянием `tactic_state`, и кучей функций для манипуляции

#check tactic
#check tactic_state

-- Основная задача тактик - преобразование выражений 
#check @expr


-- При наборе функции попробуйте вместо типа expr → bool написать {!expr → bool}
-- В VS Code появится лампочка (или Ctrl + .) со списком "hole commands"
-- Выберите "Generate a list of equations ...", все случаи для паттерн-матчинга сгенерируются автоматически
meta def is_constant_of (l : list name) : expr → bool
| (expr.const nm _) := nm ∈ l
| _ := false

#eval is_constant_of [``nat, ``int] `(ℚ)

meta def hello_world : tactic unit :=
do
  tactic.trace "Hello, ",
  tactic.trace "world!"
  
example : false :=
begin
  hello_world,
  sorry,
end

-- run_cmd "запускает" функцию с типом `tactic unit` на пустой цели
run_cmd hello_world


-- Напишем функцию, которая принимает сравнение и выдает первый и второй аргументы
meta def get_lhs_rhs : expr → option (expr × expr)
| `(%%a < %%b) := some (a, b)
| `(%%a ≤ %%b) := some (a, b)
| _            := none


-- Полезные функции: to_string, to_raw_fmt
#check to_string
#check expr.to_raw_fmt

#eval get_lhs_rhs `(20 ≤ 5)
#eval to_string $ get_lhs_rhs `(20 ≤ 5)

run_cmd tactic.trace $ get_lhs_rhs `(20 ≤ 5)

-- Напишем функцию, которая принимает выражение функции и возвращает выражение функции, где к результату добавили + 1
meta def succ_fn : expr → option expr
| (expr.lam var_name bi var_type body) := 
  let new_body := expr.app (`(nat.succ) : expr) body
  in expr.lam var_name bi var_type new_body 
| _ := none

variable α : Type
#eval to_string $ succ_fn `(λ n : ℕ, n)
