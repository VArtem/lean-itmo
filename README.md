# Формализация математики на языке Lean

Первая версия спецкурса проходит в апреле-мае 2021 года. Некоторые упражнения заимствованы из курса [Formalising Mathematics](https://github.com/ImperialCollegeLondon/formalising-mathematics) от Kevin Buzzard.

## Неделя №4 (14.05.2021)
Упражнения на теорию групп и пределы последовательностей (week_2 и week_3 курса Formalising Mathematics).

### Ресурсы:
1. [Как пользоваться `calc`](https://leanprover-community.github.io/extras/calc.html)
2. [Продолжение упражнений на теорию групп](https://github.com/ImperialCollegeLondon/formalising-mathematics/tree/master/src/week_2)

## Неделя №3 (07.05.2021)

Упражнения на формальные языки: конкатенация, замыкание Клини. Обновите репозиторий через `git pull`, чтобы увидеть новые задания.

## Неделя №2 (30.04.2021)

Четыре файла с упражнениями на множества, функции, отношения и индуктивные типы (на примере деревьев). Скачайте репозиторий с помощью `leanproject get vartem/lean-itmo` и замените `sorry` (кроме тех, что использованы для иллюстрации) на доказательства.

Для документации по тактикам можете обратиться к https://leanprover-community.github.io/mathlib_docs/tactics.html.

## Неделя №1 (23.04.2021)

Мы решали [Natural Number Game](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/). Если вы застряли, [то можно подсмотреть решения](https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/SOLUTIONS.md).

### К следующей встрече:
#### Обязательно
1. NNG: Addition + Multiplication + Function + Proposition + Adv. Proposition worlds.
2. Установить `Lean 3`, `elan` и `leanproject` по [инструкции](https://leanprover-community.github.io/get_started.html) для вашей ОС (потребуются `git` и `pip`/`pip3`). Я использую Visual Studio Code с расширением для Lean, но можно использовать и `emacs` с `lean-mode`.

#### Сделано! А еще?
1. Дорешать NNG до конца.
2. Поиграть в [еще одну короткую игру](http://wwwf.imperial.ac.uk/~buzzard/xena/max_minigame/)! Эта игра про `max a b` и неравенства.
3. Посмотреть на [репозиторий tutorials](https://github.com/leanprover-community/tutorials) с упражнениями

### Интересные видео
1. [Видео встречи на Youtube](https://www.youtube.com/watch?v=KGGCyUJr55A)
2. [Лекция The Future of Mathematics?](https://www.youtube.com/watch?v=Dp-mQ3HxgDE) от Kevin Buzzard 
3. [Демонстрация доказательства бесконечности простых чисел](https://www.youtube.com/watch?v=b59fpAJ8Mfs&list=PLlF-CfQhukNlxexiNJErGJd2dte_J1t1N&index=2)

## Полезные ссылки
* [Youtube-плейлист с записями встреч](https://www.youtube.com/playlist?list=PLlVmvffm-nlI8F9uiZ62pFyzjLvOkkYLU)
* [Главная страница leanprover-community](https://leanprover-community.github.io/)
* [Документация API mathlib](https://leanprover-community.github.io/mathlib_docs/)
* [Zulip чат, основное место для обсуждений про Lean](https://leanprover.zulipchat.com/#)
* [Twitter](https://twitter.com/xenaproject) и [блог](https://xenaproject.wordpress.com/) Kevin Buzzard про Lean
* [Репозиторий tutorials](https://github.com/leanprover-community/tutorials) с упражнениями для начинающих
* Конференция Lean for the Curious Mathematician 2020: [видео лекций](https://www.youtube.com/playlist?list=PLlF-CfQhukNlxexiNJErGJd2dte_J1t1N) и [репозиторий с упражнениями с воркшопов](https://github.com/leanprover-community/lftcm2020)

### Книги
* [Список учебных ресурсов](https://leanprover-community.github.io/learn.html) на leanprover-community
* [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/)
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/introduction.html#getting-started) и [репозиторий](https://github.com/leanprover-community/mathematics_in_lean), который можно скачать (`leanproject get mathematics_in_lean`) и интерактивно запускать код и следить за книгой