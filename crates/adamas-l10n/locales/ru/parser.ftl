# Разбор: лексер, расстановка блоков, парсер (adamas-parser).
#
# Литеральная фигурная скобка пишется во Fluent как {"{"} и {"}"}.

lex-unexpected-char = неизвестный символ
lex-unterminated-comment = незакрытый комментарий `{"{"}-`
lex-unterminated-string = незакрытый строковый литерал
lex-unknown-escape = неизвестное экранирование в строке
lex-tab-in-indentation = табуляция в отступе: отступ значим, ширина табуляции - нет

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
parse-nested-import = `import` пишется на верхнем уровне файла
parse-too-deep = вложенность глубже предела в { $limit }

misplaced-when = `when` пишется в объявлении класса, перед суперклассами: `class Ord a when Eq a where …`
misplaced-using = `using` пишется в выражении, перед инстансом: `using p (f x)`
misplaced-braces = фигурные скобки здесь ничего не открывают: effect row пишется `{"{"}Ask{"}"} A`, тип записи - `{"{"}x : A{"}"}`, группа implicit-связываний - `{"{"}a : Type{"}"}`; пустой row не пишется
parse-misplaced = { $what }
