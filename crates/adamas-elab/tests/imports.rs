//! Программа из нескольких файлов: `import`, порядок между файлами (§4.8).
//!
//! # Свидетель обязан ломаться от сломанного разрешения
//!
//! У многофайловости свой жанр подделки: программа из двух файлов, где второй
//! ничего не отдаёт, проверяется и при начисто сломанном импорте. Поэтому
//! каждый свидетель здесь **парный**: та же программа без `import` обязана быть
//! отвергнута «имя не найдено». Пара и есть различение - без неё зелёный тест
//! говорил бы только о том, что текст разобрался.
//!
//! Путей разрешения два, и они разные: квалифицированный доступ идёт через
//! точечное имя, открытое - через лестницу коротких имён. Тест на одном зелен
//! при сломанном другом, поэтому проверяются оба.

use adamas_core::source::SourceFile;
use adamas_elab::program::{Memory, Program, analyze};

/// Модуль, который что-то отдаёт: семейство, конструкторы и функция над ними.
const NUMBERS: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

double : Nat -> Nat
double Zero = Zero
double (Succ k) = Succ (Succ (double k))
";

/// Программа с входным файлом `вход` и одним модулем в памяти.
fn program(entry: &str, modules: &Memory) -> Program {
    analyze(SourceFile::new("вход", entry.to_owned()), modules)
}

/// Программа, которую проход принял. Отказ - провал теста.
fn accepted(entry: &str, modules: &Memory) -> Program {
    let program = program(entry, modules);
    if let Some(located) = program.error() {
        panic!("отвергнуто: {}", program.rendered(located));
    }
    program
}

/// Текст отказа. Принятая программа - провал теста.
fn refused(entry: &str, modules: &Memory) -> String {
    let program = program(entry, modules);
    let Some(located) = program.error() else {
        panic!("ожидался отказ");
    };
    located.diagnostic.message()
}

/// Модули по умолчанию: один `Numbers`.
fn numbers() -> Memory {
    Memory::new().with("Numbers", NUMBERS)
}

#[test]
fn a_qualified_name_comes_from_the_imported_file() {
    // §4.8: доступ через `Map.insert`. Здесь - `Numbers.double`, и в самом
    // входном файле такого имени нет ни в каком виде.
    let entry = "\
import Numbers as N

main : N.Nat
main = N.double (N.Succ N.Zero)
";
    let program = accepted(entry, &numbers());
    let signature = program.signature.as_ref().expect("сигнатура");
    assert!(
        signature.lookup("Numbers.double").is_some(),
        "член подключённого файла обязан стоять под своим путём"
    );
    assert!(
        signature.lookup("main").is_some(),
        "входной файл квалификации не получает: он и есть программа"
    );

    // Вторая половина пары: без `import` то же имя не находится. Ломающий
    // разрешение мутант («не искать в подключённом») даёт ровно этот текст.
    let without = entry.replace("import Numbers as N\n", "");
    let why = refused(&without, &numbers());
    assert!(
        why.contains("N.Nat") || why.contains('N'),
        "без импорта имя обязано не находиться, сказано: {why}"
    );
}

#[test]
fn an_open_list_brings_names_in_unqualified() {
    // Второй путь разрешения: лестница коротких имён, а не точечное имя.
    // Семейство открывается вместе с конструкторами - тем же правилом, каким
    // §4.8 поднимает их из тела модуля.
    let entry = "\
import Numbers (Nat, double)

main : Nat
main = double (Succ (Succ Zero))
";
    accepted(entry, &numbers());

    let without = entry.replace("import Numbers (Nat, double)\n", "");
    let why = refused(&without, &numbers());
    assert!(
        why.contains("Nat"),
        "без импорта короткое имя обязано не находиться, сказано: {why}"
    );
}

#[test]
fn an_open_list_is_checked_against_what_the_module_declares() {
    // Открытое имя, которого в модуле нет, - отказ с названным модулем, а не
    // тихая пустая привязка, всплывающая в месте использования.
    let why = refused("import Numbers (triple)\n", &numbers());
    assert!(
        why.contains("Numbers") && why.contains("triple"),
        "сказано: {why}"
    );
}

#[test]
fn a_module_that_is_not_imported_is_not_reachable_by_its_path() {
    // Явные зависимости (§7.3): `Hidden` объявлен в программе - его подключил
    // `Numbers`, - но входной файл его не импортировал, и написанный путь к
    // нему не разрешается.
    let modules = Memory::new()
        .with(
            "Numbers",
            &format!("import Hidden (Tag)\n\n{NUMBERS}\n\nmark : Tag\nmark = Mark\n"),
        )
        .with("Hidden", "data Tag where\n  Mark : Tag\n");
    let entry = "\
import Numbers as N

main : N.Nat
main = N.double N.Zero
";
    accepted(entry, &modules);

    let reaching = "\
import Numbers as N

main : Hidden.Tag
main = Hidden.Mark
";
    let why = refused(reaching, &modules);
    assert!(
        why.contains("Hidden"),
        "путь к неимпортированному модулю обязан не разрешаться, сказано: {why}"
    );
}

#[test]
fn an_import_enters_the_order_of_the_file() {
    // §10 вопрос 178: импорт - объявление, и стоит он в том же порядке, что
    // прочие. Написанное **выше** импорта его имён не видит - это то же
    // ordered scoping, что §4.8 задаёт внутри файла.
    let above = "\
main : Nat
main = double Zero

import Numbers (Nat, Zero, double)
";
    let why = refused(above, &numbers());
    assert!(
        why.contains("Nat"),
        "имя выше импорта обязано не находиться, сказано: {why}"
    );

    // Тот же текст с импортом наверху принимается: различает эти две программы
    // ровно порядок, и ничего больше.
    let below = "\
import Numbers (Nat, Zero, double)

main : Nat
main = double Zero
";
    accepted(below, &numbers());
}

#[test]
fn a_cycle_of_imports_is_refused_by_name() {
    // Порядка у кольца нет, а выразить взаимную видимость между файлами нечем:
    // `mutual` живёт внутри файла. Отказ поэтому называет кольцо целиком.
    let modules = Memory::new()
        .with(
            "Left",
            "import Right (Tock)\n\ndata Tick where\n  Tick : Tock -> Tick\n",
        )
        .with(
            "Right",
            "import Left (Tick)\n\ndata Tock where\n  Tock : Tick -> Tock\n",
        );
    let why = refused("import Left (Tick)\n", &modules);
    assert!(
        why.contains("цикл") && why.contains("Left") && why.contains("Right"),
        "сказано: {why}"
    );
}

#[test]
fn a_missing_module_names_where_it_was_looked_for() {
    let why = refused("import Data.Map as Map\n", &numbers());
    assert!(
        why.contains("Data.Map"),
        "отказ обязан назвать путь, сказано: {why}"
    );
}

#[test]
fn a_diamond_declares_the_shared_module_once() {
    // Два файла подключают третий; объявляется он один раз, и тип из него
    // остаётся **тем же** - иначе `Left.wrap` и `Right.wrap` не сходились бы.
    let modules = Memory::new()
        .with("Base", "data Tag where\n  Mark : Tag\n")
        .with(
            "Left",
            "import Base (Tag, Mark)\n\nleft : Tag\nleft = Mark\n",
        )
        .with(
            "Right",
            "import Base (Tag)\n\npass : Tag -> Tag\npass t = t\n",
        );
    let entry = "\
import Left as L
import Right as R
import Base (Tag)

main : Tag
main = R.pass L.left
";
    let program = accepted(entry, &modules);
    let signature = program.signature.as_ref().expect("сигнатура");
    assert!(
        signature.lookup("Base.Tag").is_some(),
        "общий модуль объявлен под своим путём"
    );
    // Файлов ровно четыре: вход и три модуля. Повторное объявление дало бы
    // пятый - и второй, несовместимый `Base.Tag`. Прелюдия в счёт не входит:
    // подключается она неявно каждому файлу (§4.4), автор её не писал.
    let written = program
        .units
        .iter()
        .filter(|it| it.path.as_deref() != Some(adamas_elab::program::PRELUDE))
        .count();
    assert_eq!(written, 4, "общий модуль подключён дважды");
}

#[test]
fn a_class_declared_in_an_imported_file_is_a_name_of_the_program() {
    // §4.4: классы доступны без импорта, а §3.5 меряет непересекаемость
    // инстансов по всей программе. Значит класс квалификации файла не получает,
    // и метод его зовётся коротким именем.
    let modules = Memory::new().with(
        "Classes",
        "\
data Bool where
  False : Bool
  True : Bool

class Eqv a where
  eq : a -> a -> Bool

instance Eqv Bool where
  eq False False = True
  eq True True = True
  eq x y = False
",
    );
    let entry = "\
import Prelude
import Classes (Bool, True)

main : Bool
main = eq True True
";
    let program = accepted(entry, &modules);
    let signature = program.signature.as_ref().expect("сигнатура");
    assert!(
        signature.lookup("eq").is_some(),
        "метод класса - имя программы, а не член файла"
    );
}

#[test]
fn a_mutual_block_is_refused_inside_an_imported_file() {
    // Названная граница, а не умолчание: члены группы объявляются одним
    // вызовом, а квалифицировать их он не умеет. Объяви их неквалифицированно -
    // и `M.eval` снаружи не нашлось бы, а два файла с одноимённой группой
    // столкнулись бы. Отказ поэтому стоит здесь, и пока он стоит, взаимная
    // рекурсия между файлами невыразима - отсюда и отказ кольцу выше.
    let modules = Memory::new().with(
        "Grouped",
        "\
mutual
  data Tick where
    Wind : Tock -> Tick

  data Tock where
    Turn : Tick -> Tock
",
    );
    let why = refused("import Grouped (Tick)\n", &modules);
    assert!(
        why.contains("mutual") && why.contains("импортированном файле"),
        "сказано: {why}"
    );

    // Тот же блок на верхнем уровне входного файла законен: квалификации там
    // нет, и объявлять члены группы нечем мешать.
    accepted(
        "\
mutual
  data Tick where
    Wind : Tock -> Tick

  data Tock where
    Turn : Tick -> Tock
",
        &Memory::new(),
    );
}
