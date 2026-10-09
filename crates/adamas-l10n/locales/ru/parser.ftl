# Разбор: лексер, расстановка блоков, парсер (adamas-parser).
#
# Литеральная фигурная скобка пишется во Fluent как {"{"} и {"}"}.

lex-unexpected-char = неизвестный символ
lex-unterminated-comment = незакрытый комментарий `{"{"}-`
lex-unterminated-string = незакрытый строковый литерал
lex-unknown-escape = неизвестное экранирование в строке
lex-bad-char = символьный литерал - ровно один символ в одинарных кавычках: `'a'`, `'\n'`, `'\u{"{"}1F600{"}"}'`
lex-tab-in-indentation = табуляция в отступе: отступ значим, ширина табуляции - нет
lex-bad-backtick = в обратных кавычках пишется имя функции: «x `div` y» значит «div x y»

layout-shallow-block = тело блока должно быть с большим отступом, чем окружающий блок
layout-empty-block = после ключевого слова нет тела блока
layout-left-of-file = лексема левее первой в файле: блок файла закрывается только концом файла
layout-block-in-brackets = блок внутри скобок: layout там выключен
layout-unclosed-bracket = незакрытая скобка
layout-unmatched-bracket = закрывающая скобка без открывающей
layout-mismatched-bracket = скобка закрыта не тем видом скобки

token-ident = идентификатор
token-operator = оператор
token-nat = натуральный литерал
token-float = литерал с плавающей точкой
token-str = строковый литерал
token-char = символьный литерал
token-open = начало блока
token-sep = граница блока
token-close = конец блока
token-eof = конец файла

expected-declaration = объявление
expected-expression = выражение
expected-pattern = паттерн
expected-name = имя

parse-empty-record = пустая запись: `{"{"}{"}"}` не различает тип и значение
parse-precedence = приоритет пишется числом от 0 до 9
parse-mixed-record = запись либо объявляет поля, либо присваивает им значения
parse-expected = ожидается { $expected }, а не { $found }
parse-expected-fn = после ABI в `extern` пишется `fn`
parse-attributed-export = атрибут пишется при сигнатуре определения, а не при `export`
parse-pattern-path = `{ $path }`: путь в паттерне называет конструктор, а он пишется с заглавной
parse-field-multiplicity = кратность пишется у поля в типе записи (`{"{"} ω x : A {"}"}`), а не у значения
parse-multiplicity = кратность записывается `0`, `1` или `ω`
parse-duplicate-state = `state`: начальное состояние написано дважды
parse-split-clauses = клаузы `{ $name }` разделены другим объявлением
parse-block-not-last = после формы с блоком на строке ничего не пишется: где она кончается, видно только по отступу
parse-wildcard = wildcard-импорта нет: открытые имена перечисляются по одному
parse-haskell-data = тип объявляется не через `=`: конструкторы перечисляются после `where`, каждый своей строкой со своим типом - эта же декларация по-нашему ниже{ $suggestion }
parse-haskell-data-generic = тип объявляется не через `=`: конструкторы перечисляются после `where`, каждый своей строкой со своим типом - `data Box a where`, а строкой ниже `MkBox : a -> Box a`
parse-nested-import = `import` пишется на верхнем уровне файла
parse-too-deep = вложенность глубже предела в { $limit }

misplaced-when = `when` пишется в объявлении класса, перед суперклассами: `class Ord a when Eq a where …`
misplaced-using = `using` пишется в выражении, перед инстансом: `using p (f x)`
misplaced-braces = фигурные скобки здесь ничего не открывают: effect row пишется `{"{"}Ask{"}"} A`, тип записи - `{"{"}x : A{"}"}`, группа implicit-связываний - `{"{"}a : Type{"}"}`; пустой row не пишется
misplaced-context = контекст ограничений пишется в фигурных скобках: `{"{"}Eq a{"}"} => a -> Bool`, несколько - через запятую: `{"{"}Eq a, Show a{"}"} => …`
misplaced-superclass = суперкласс пишется после `when`, а не перед `=>`: `class Ord a when Eq a where …`
misplaced-section-operand = операнд секции - применение либо выражение в своих скобках: `(+ f x)`, `(* (a + b))`; фикситетов разбор не знает
misplaced-minus-section = `(- e)` - не секция: в Haskell это отрицание; вычитание из аргумента пишется `(\v -> v - e)`, отрицание - `0 - e`
misplaced-open-guards = последний гард - `otherwise`: провала к следующей клаузе нет, и случай, не покрытый гардами, остался бы без ответа
parse-misplaced = { $what }
