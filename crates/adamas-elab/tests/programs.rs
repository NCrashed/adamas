//! Программы Adamas от текста до проверки типов - milestone Фазы 2.
//!
//! Проверяется не форма собранного терма, а два факта: программа доходит до
//! сигнатуры и то, что в ней оказалось, **вычисляет то, что написано**.
//! Форма - деталь элаборации, и тест на неё ломался бы от смены стратегии,
//! ничего при этом не защищая.

use std::rc::Rc;

use adamas_core::check::{ErrorKind, check_closed};
use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Rows, Term};
use adamas_elab::{ElabError, Missing, elaborate};
use adamas_parser::parse;

/// Текст до сигнатуры. Отказ здесь - провал теста, а не проверяемый исход.
fn program(text: &str) -> Signature {
    let module = match parse(text) {
        Ok(module) => module,
        Err(error) => panic!("не разобралось: {error}"),
    };
    match elaborate(&module) {
        Ok(signature) => signature,
        Err(error) => panic!("не элаборировалось: {error}"),
    }
}

/// Отказ элаборации; всё остальное - провал теста.
fn refused(text: &str) -> ElabError {
    let module = match parse(text) {
        Ok(module) => module,
        Err(error) => panic!("не разобралось: {error}"),
    };
    match elaborate(&module) {
        Err(error) => error,
        Ok(_) => panic!("ожидался отказ элаборации"),
    }
}

/// Ссылка на определение с одним параметром уровня, взятым нулём.
///
/// Написанный `Type` даёт дырку, она обобщается в параметр, и семейство
/// оказывается полиморфным по уровню. Тесту нужен замкнутый терм, поэтому
/// уровень задаётся явно.
fn at(name: &str) -> Term {
    Term::Const(name.into(), Rc::from([Level::Zero]), pure())
}

/// Ссылка на определение без аргументов уровня.
///
/// Конструктор так не пишется: подъём его типа не трогает, row-параметра у
/// него нет, и лишний аргумент разошёлся бы с тем, что стоит в теле.
fn to(name: &str) -> Term {
    Term::Const(name.into(), Rc::from([]), pure())
}

/// Аргументы-row замкнутого терма: подъём (§3.4) даёт параметр всякой
/// написанной сигнатуре, и ссылка на неё обязана его заполнить. Тест строит
/// терм руками, эффектов в нём нет, поэтому все они пусты; лишние арностью
/// отбрасываются, и одного хватает на любое определение этого файла.
fn pure() -> Rows {
    Rows::new([Row::empty()])
}

/// `Nat` и `Bool` - минимальная база, на которой пишется всё остальное.
const BASE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat
";

#[test]
fn a_family_and_its_constructors_reach_the_signature() {
    let signature = program(BASE);
    assert_eq!(
        signature
            .constructors("Nat")
            .expect("Nat индуктивен")
            .iter()
            .map(std::convert::AsRef::as_ref)
            .collect::<Vec<&str>>(),
        ["Zero", "Succ"],
        "порядок объявления задаёт порядок ветвей разбора"
    );
}

#[test]
fn a_definition_by_clauses_computes_what_it_says() {
    // `plus` собирается в дерево разбора и **вычисляет**: проверка
    // `anything (plus 2 3)` против `P 5` проходит только через δ и ι.
    let text = format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)
"
    );
    let signature = program(&text);

    assert!(
        signature
            .lookup("plus")
            .is_some_and(|definition| definition.total),
        "структурная рекурсия распознана"
    );

    let number = |value: u32| {
        (0..value).fold(Term::constant("Zero"), |term, _| {
            Term::constant("Succ").apply([term])
        })
    };
    // `P` написана через `Type`, поэтому полиморфна по уровню; уровень здесь
    // задаётся явно - тесту нужен замкнутый терм, а не ещё одна дырка.
    for (left, right, sum) in [(0, 0, 0), (2, 3, 5), (4, 1, 5)] {
        let witness = at("anything").apply([number(sum)]);
        let family = at("P").apply([to("plus").apply([number(left), number(right)])]);
        let outcome = check_closed(&signature, &witness, &family);
        assert!(outcome.is_ok(), "{left}+{right} = {sum}: {outcome:?}");
    }
}

#[test]
fn nested_patterns_and_a_wildcard_elaborate() {
    let text = format!(
        "{BASE}
Q : Bool -> Type
q : (0 b : Bool) -> Q b

even : Nat -> Bool
even Zero = True
even (Succ Zero) = False
even (Succ (Succ k)) = even k

constant : Nat -> Bool
constant _ = True
"
    );
    let signature = program(&text);

    // Что дерево разбора **вычисляет**, видно только через конвертируемость:
    // `normalize` определений не разворачивает, δ живёт в проверке типов.
    for (input, expected) in [(0, "True"), (1, "False"), (2, "True"), (3, "False")] {
        let number = (0..input).fold(Term::constant("Zero"), |term, _| {
            Term::constant("Succ").apply([term])
        });
        let witness = at("q").apply([Term::constant(expected)]);
        let stated = at("Q").apply([to("even").apply([number])]);
        let outcome = check_closed(&signature, &witness, &stated);
        assert!(outcome.is_ok(), "even {input} = {expected}: {outcome:?}");
    }
    // `_` связывает, ничего не называя: тело обязано считаться так же, как
    // если бы аргумента не было вовсе.
    let witness = at("q").apply([Term::constant("True")]);
    let stated = at("Q").apply([to("constant").apply([Term::constant("Zero")])]);
    assert!(check_closed(&signature, &witness, &stated).is_ok());
}

#[test]
fn an_indexed_family_elaborates() {
    // Индексы монотипны, поэтому фрагменту доступны: параметров у семейства
    // нет, а `Nat` в индексе объявлен выше.
    let text = format!(
        "{BASE}
data Even : Nat -> Type where
  EvenZero : Even Zero
  EvenTwo : (0 n : Nat) -> Even n -> Even (Succ (Succ n))
"
    );
    let signature = program(&text);
    assert_eq!(
        signature
            .constructors("Even")
            .expect("Even индуктивен")
            .len(),
        2
    );
}

#[test]
fn a_signature_without_clauses_is_a_postulate() {
    // §4.1 пишет так примитивы: `openFile : String -> …` без тела.
    let text = format!("{BASE}\nopaque : Nat -> Bool\n");
    let signature = program(&text);
    let postulate = signature.lookup("opaque").expect("постулат объявлен");
    assert!(postulate.body.is_none(), "тела у постулата нет");
}

#[test]
fn a_dependent_function_type_elaborates() {
    let text = format!(
        "{BASE}
P : Nat -> Type
witness : (0 n : Nat) -> P n
use : (0 n : Nat) -> P n
use n = witness n
"
    );
    let signature = program(&text);
    // Зависимость дожила до тела: `use Zero` обязана иметь тип `P Zero`, а не
    // `P n` при каком-нибудь другом `n`.
    let stated = at("P").apply([Term::constant("Zero")]);
    let witness = at("use").apply([Term::constant("Zero")]);
    assert!(check_closed(&signature, &witness, &stated).is_ok());
}

#[test]
fn a_let_with_an_annotation_elaborates() {
    let text = format!(
        "{BASE}
two : Nat
two =
  let one : Nat = Succ Zero
  Succ one
"
    );
    let signature = program(&text);
    let body = signature
        .lookup("two")
        .and_then(|definition| definition.body.clone())
        .expect("тело есть");
    assert_eq!(
        adamas_core::eval::normalize(&body).to_string(),
        "Succ (Succ Zero)",
        "`let` вычисляется"
    );
}

#[test]
fn a_lambda_takes_its_multiplicity_from_the_written_type() {
    // Кратность лямбды обязана совпасть с кратностью `Pi`, а вывести её
    // элаборация не может. Выводить и нечего: тип написан, спайн его виден.
    let text = format!(
        "{BASE}
id : (1 n : Nat) -> Nat
id = \\n -> n

first : (1 x : Nat) -> (0 y : Nat) -> Nat
first = \\x -> \\y -> x

second : (0 x : Nat) -> (1 y : Nat) -> Nat
second = \\x y -> y

local : Nat
local =
  let same : (1 n : Nat) -> Nat = \\n -> n
  same (Succ Zero)
"
    );
    let signature = program(&text);
    let body = signature
        .lookup("local")
        .and_then(|definition| definition.body.clone())
        .expect("тело есть");
    assert_eq!(
        adamas_core::eval::normalize(&body).to_string(),
        "Succ Zero",
        "лямбда под `1`-связыванием не только объявляется, но и считает"
    );
}

#[test]
fn an_operator_chain_elaborates() {
    // Один оператор в цепочке - это два применения; фикситетов ещё нет,
    // поэтому длиннее цепочка не собирается (см. таблицу `Missing`).
    let text = format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

(+) : Nat -> Nat -> Nat
(+) Zero m = m
(+) (Succ k) m = Succ (k + m)
"
    );
    let signature = program(&text);
    let number = |value: u32| {
        (0..value).fold(Term::constant("Zero"), |term, _| {
            Term::constant("Succ").apply([term])
        })
    };
    let witness = at("anything").apply([number(3)]);
    let stated = at("P").apply([to("+").apply([number(1), number(2)])]);
    assert!(
        check_closed(&signature, &witness, &stated).is_ok(),
        "1 + 2 = 3"
    );
}

#[test]
fn a_binder_group_does_not_see_its_own_names() {
    // `A` в `(x y : A)` написано раньше обоих имён: видеть их оно не может,
    // хотя элаборируется под ними - индексы де Брёйна того требуют.
    let text = format!(
        "{BASE}
f : (0 t : Type) -> (0 t x : t) -> Nat
f a b c = Zero
"
    );
    let signature = program(&text);
    assert!(signature.lookup("f").is_some(), "группа не захватила себя");
}

#[test]
fn a_recursive_definition_sees_its_own_level_arity() {
    // Арность параметров уровня считается по проверенному типу: `is_type`
    // решает часть дырок, и самоссылка обязана получить столько же аргументов,
    // сколько у члена окажется параметров.
    let text = format!(
        "{BASE}
Id : Type -> Type

f : Id Nat -> Id Nat
f x = f x
"
    );
    let signature = program(&text);
    assert!(signature.lookup("f").is_some());
}

#[test]
fn one_name_gets_one_set_of_level_holes() {
    // Полиморфное по уровню семейство: два вхождения в одной сигнатуре обязаны
    // получить один параметр, иначе тождество над ним не пишется.
    let text = "\
data D : Type where
  C : D

f : D -> D
f x = x
";
    let signature = program(text);
    let body = signature
        .lookup("f")
        .and_then(|definition| definition.body.clone())
        .expect("тело есть");
    // Печать ядра - аварийная, на индексах: имя в ней не участвует.
    assert_eq!(
        adamas_core::eval::normalize(&body).to_string(),
        "\\(ω x) -> #0",
        "тождество собралось"
    );
}

// ------------------------------------------------------------------ отказы

#[test]
fn an_uppercase_name_in_a_pattern_must_be_a_constructor() {
    // Ровно та опечатка, ради которой правило регистра и выбрано: `Zeroo` не
    // становится переменной, ловящей всё, а называется на месте.
    let text = format!(
        "{BASE}
f : Nat -> Bool
f Zeroo = True
f _ = False
"
    );
    let error = refused(&text);
    let ElabError::NotAConstructor { name, .. } = &error else {
        panic!("ожидалось `NotAConstructor`, получено {error:?}");
    };
    assert_eq!(&**name, "Zeroo");
}

#[test]
fn a_lowercase_name_in_a_pattern_binds() {
    // Контроль к предыдущему: строчное имя связывает, даже если совпадает с
    // конструктором по смыслу.
    let text = format!(
        "{BASE}
f : Nat -> Nat
f zero = zero
"
    );
    let signature = program(&text);
    assert!(signature.lookup("f").is_some());
}

#[test]
fn clauses_without_a_signature_are_refused() {
    let text = format!("{BASE}\nf Zero = True\n");
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::MissingSignature { .. }),
        "получено {error:?}"
    );
}

#[test]
fn what_the_core_cannot_carry_yet_names_itself() {
    // Каждая форма отвечает тем, чего ей недостаёт, а не «неизвестное имя»:
    // программа написана правильно, не хватает ядра.
    // Таблица покрывает варианты целиком: непокрытый вариант - это форма,
    // про которую никто не проверял, что она вообще досюда доходит.
    let missing = [
        (
            "f : Nat\nf =\n  let x : a = Zero\n  x\n",
            Missing::FreeTypeVariable,
        ),
        ("f : Nat -> Nat\nf x = 1\n", Missing::Literal),
        ("f : Nat\nf =\n  let x = Zero\n  x\n", Missing::UntypedLet),
        (
            "f : Nat -> Nat\nf = \\(0 x : Nat) -> x\n",
            Missing::LambdaAnnotation,
        ),
        (
            "f : Nat -> Nat\nf = \\(Cons x xs) -> Zero\n",
            Missing::LambdaPattern,
        ),
        ("f : Nat\nf = (Zero, Zero)\n", Missing::Tuple),
        ("f : Nat\nf = ()\n", Missing::Unit),
        ("f : Nat\nf = [Zero]\n", Missing::List),
        ("f : Nat\nf = Zero + Zero + Zero\n", Missing::Fixities),
        (
            "f : Nat -> Nat\nf x = y\n  where\n    y : Nat\n    y = x\n",
            Missing::LocalDefinitions,
        ),
    ];
    for (text, expected) in missing {
        let text = format!("{BASE}{text}");
        let error = refused(&text);
        let ElabError::Missing { what, .. } = error else {
            panic!("для {text:?} ожидалось `Missing`, получено {error:?}");
        };
        assert_eq!(what, expected, "для {text:?}");
    }
}

#[test]
fn a_repeated_variable_in_a_clause_is_refused() {
    // Равенство аргументов паттерном не выражается: терм собрался бы
    // корректный, с правым вхождением, и ядро принимало бы опечатку.
    let text = format!("{BASE}f : Nat -> Nat -> Nat\nf x x = x\n");
    let error = refused(&text);
    let ElabError::RepeatedBinding { name, .. } = &error else {
        panic!("ожидалось `RepeatedBinding`, получено {error:?}");
    };
    assert_eq!(&**name, "x");
    // `_` повтором не считается: он не называет.
    let text = format!("{BASE}g : Nat -> Nat -> Nat\ng _ _ = Zero\n");
    assert!(program(&text).lookup("g").is_some());
}

#[test]
fn an_uppercase_name_does_not_bind() {
    // §4.1: заглавное имя ссылается на объявленное. Связать им - заслонить
    // то, на что оно ссылается, и `Zero` внутри блока перестал бы быть
    // конструктором.
    for text in [
        "f : (Zero : Nat) -> Nat\nf n = n\n",
        "f : Nat\nf =\n  let Zero : Nat = Succ Zero\n  Zero\n",
    ] {
        let text = format!("{BASE}{text}");
        let error = refused(&text);
        assert!(
            matches!(error, ElabError::UppercaseBinding { .. }),
            "для {text:?} получено {error:?}"
        );
    }
}

#[test]
fn a_signature_apart_from_its_clauses_is_refused_by_name() {
    // Примыкание - требование реализации: сигнатура, за которой сразу не пошли
    // клаузы, становится постулатом. Отказ обязан называть настоящую причину,
    // а не «нет сигнатуры».
    let text = format!("{BASE}f : Nat -> Nat\ng : Nat -> Nat\ng x = x\nf x = x\n");
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::DetachedSignature { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_block_must_end_with_a_value() {
    let text = format!("{BASE}f : Nat\nf =\n  let x : Nat = Zero\n");
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::BlockWithoutValue { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_free_type_variable_of_a_signature_is_lifted() {
    // §4.1: свободное имя сигнатуры - implicit-параметр. Проверяется не форма
    // поднятого типа, а то, что за ней следует: определение применимо к
    // значениям разных типов, и аргумент к нему никто не писал.
    let signature = program(&format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

identity : a -> a
identity x = x

one : Nat
one = identity (Succ Zero)

yes : Bool
yes = identity True
"
    ));
    // Одно определение при двух разных типах аргумента - это и значит, что
    // параметр поднялся: писать его никто не писал.
    let one = to("one");
    let outcome = check_closed(
        &signature,
        &at("anything").apply([Term::constant("Succ").apply([Term::constant("Zero")])]),
        &at("P").apply([one]),
    );
    assert!(outcome.is_ok(), "поднятое вычисляет: {outcome:?}");

    // В теле то же имя - опечатка, а не свободная переменная: поднимается
    // сигнатура объявления, а тело от неё уже связано.
    let error = refused(&format!("{BASE}f : Nat -> Nat\nf n = a\n"));
    assert!(
        matches!(error, ElabError::UnknownName { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_lifted_parameter_is_written_with_an_at_sign() {
    // §4.1: `@` пишет то, что иначе вывелось бы. Написанное и выведенное дают
    // одно определение - это и есть проверяемое, а не форма терма.
    let signature = program(&format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

identity : a -> a
identity x = x

written : Nat
written = identity @Nat Zero
"
    ));
    let outcome = check_closed(
        &signature,
        &at("anything").apply([Term::constant("Zero")]),
        &at("P").apply([to("written")]),
    );
    assert!(outcome.is_ok(), "написанное вычисляет так же: {outcome:?}");

    // Явному связыванию `@` не соответствует: аргумент туда пишется обычным
    // применением, и подмена одного другим - ошибка, а не вкус.
    let error = refused(&format!(
        "{BASE}f : Nat -> Nat\nf n = n\n\ng : Nat\ng = f @Nat Zero\n"
    ));
    assert!(
        matches!(error, ElabError::NoImplicitParameter { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_field_multiplicity_follows_how_the_scrutinee_is_bound() {
    // §4.1 назначает полю конструктора кратность `1` и обещает, что обычный
    // код изменения не замечает. Держится обещание на правиле разбора (§3.3):
    // поле приходит в ветвь при `q · r`, где `r` - кратность связывания
    // разбираемого. Оба случая написаны рядом, потому что порознь каждый
    // читается как случайность.
    let pair = format!(
        "{BASE}
data Pair where
  MkPair : Bool -> Bool -> Pair

and : Bool -> Bool -> Bool
and True b = b
and False _ = False
"
    );

    // ω-связывание: `1 · ω = ω`, поле неограниченно.
    let signature = program(&format!(
        "{pair}\nboth : Pair -> Bool\nboth (MkPair x y) = and x x\n"
    ));
    assert!(signature.lookup("both").is_some());

    // Явно линейное связывание: `1 · 1 = 1`. Это названная цена решения - `r`
    // следует связыванию, а не содержимому.
    let error = refused(&format!(
        "{pair}\nonce : (1 p : Pair) -> Bool\nonce (MkPair x y) = and x x\n"
    ));
    let Some(core) = error.core() else {
        panic!("ожидался отказ ядра, получено {error:?}");
    };
    assert!(
        matches!(core.kind, ErrorKind::UsageViolation { .. }),
        "получено {core:?}"
    );
}

#[test]
fn an_ill_typed_program_is_refused_by_the_core() {
    // Элаборация не в TCB: терм она собирает, а отвергает его `check`.
    let text = format!("{BASE}\nf : Nat -> Bool\nf n = n\n");
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

// ------------------------------------------------------------------ владение

/// `File` - ресурс с конструктором и деструктором, `closeFile` линейна.
///
/// Линейность `closeFile` не украшение: поле `Open` имеет кратность `1`
/// (§4.1), разбор ресурсного связывания идёт при `r = 1`, и поле приходит в
/// ветвь линейным - ω-функция его не примет.
const RESOURCE: &str = "\
resource File where
  Open : Bool -> File
  drop : File -> Bool
  drop (Open b) = closeFile b
";

#[test]
fn a_record_does_not_hold_a_resource() {
    // Держателем владеемого поля обязан быть владеемый тип (§3.3, вопрос 77),
    // и у записи исключений нет: объявляется она `type`, деструктора не имеет,
    // связывание её `ω`. Запись была единственным обходом правила - поле
    // проецировалось сколько угодно раз, то есть дескриптор закрывался дважды,
    // а забытая запись не закрывала его ни разу. Прямой аналог на `data`
    // отвергался всегда.
    let error = refused(&format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
type Box = {{ h : File }}
"
    ));
    assert!(
        matches!(error, ElabError::OwnedRecordField { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_resource_declares_a_family_and_its_destructor() {
    let text = format!("{BASE}\ncloseFile : (1 b : Bool) -> Bool\ncloseFile b = b\n\n{RESOURCE}");
    let signature = program(&text);
    assert_eq!(
        signature
            .constructors("File")
            .expect("File индуктивен")
            .iter()
            .map(std::convert::AsRef::as_ref)
            .collect::<Vec<&str>>(),
        ["Open"],
        "голая сигнатура в теле - конструктор"
    );
    assert!(
        signature
            .lookup("drop")
            .is_some_and(|definition| definition.body.is_some()),
        "сигнатура с клаузами в теле - определение"
    );
}

#[test]
fn a_binding_of_an_owned_type_is_linear_without_being_written() {
    // Правило §3.3: связывание unique- или resource-типа получает `1` само.
    // Видно это по тому, что ω-функция от ресурса не типизируется: аргумент
    // объявлен `1`, а `use` требует ω.
    let preamble = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
and : (1 x : Bool) -> (1 y : Bool) -> Bool
and x y = x

share : (ω f : Bool) -> Bool
share f = f
"
    );

    let signature = program(&format!(
        "{preamble}\nclose : File -> Bool\nclose h = drop h\n"
    ));
    assert!(signature.lookup("close").is_some(), "один разбор законен");

    // Два - нет: `h` связано при `1`, хотя писать `1` не пришлось.
    // Позиция ω-аргумента - тоже нет, и это ровно та дыра, ради которой §3.3
    // говорит «вредно только попадание значения в ω-позицию»: масштабирование
    // доводит одно использование до ω.
    for (what, text) in [
        (
            "дважды",
            "twice : File -> Bool\ntwice h = and (drop h) (drop h)\n",
        ),
        (
            "в ω-позиции",
            "wide : File -> Bool\nwide h = share (drop h)\n",
        ),
    ] {
        let error = refused(&format!("{preamble}\n{text}"));
        let Some(core) = error.core() else {
            panic!("{what}: ожидался отказ ядра, получено {error:?}");
        };
        assert!(
            matches!(core.kind, ErrorKind::UsageViolation { .. }),
            "{what}: получено {core:?}"
        );
    }
}

#[test]
fn an_unrestricted_binding_of_an_owned_type_is_refused() {
    // Дыра ω→1 закрыта не проверкой значения, а отсутствием её предмета:
    // ω-связывания такого типа не бывает, и отказ стоит на самом связывании.
    for (text, what) in [
        (
            format!(
                "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
kept : (ω h : File) -> Bool
kept h = True
"
            ),
            "resource",
        ),
        (
            format!(
                "{BASE}
unique data Buffer where
  MkBuffer : Bool -> Buffer

kept : (ω a : Buffer) -> Bool
kept a = True
"
            ),
            "unique",
        ),
    ] {
        let error = refused(&text);
        assert!(
            matches!(error, ElabError::UnrestrictedOwned { .. }),
            "{what}: получено {error:?}"
        );
    }
}

#[test]
fn an_erased_binding_of_an_owned_type_is_allowed() {
    // `0` законно: стёртое упоминание в доказательстве ничего не потребляет,
    // и запрещать его значило бы запретить говорить о ресурсе в типах.
    let text = format!(
        "{BASE}
unique data Buffer where
  MkBuffer : Bool -> Buffer

P : (0 a : Buffer) -> Type
mention : (0 a : Buffer) -> P a
"
    );
    assert!(program(&text).lookup("mention").is_some());
}

#[test]
fn an_owned_type_is_not_declared_at_the_top_level() {
    // Определение верхнего уровня всегда `ω` - линейности на всю программу
    // ядро не считает, - а §3.3 требует владеемому связыванию `1`. Постулат
    // ресурсного типа поэтому был бы обычным ω-именем: `drop` по нему зовётся
    // сколько угодно раз, то есть один объект закрывается дважды.
    let preamble = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}"
    );
    for text in [
        "\ntheFile : File\n",
        "\ntheFile : File\ntheFile = Open True\n",
        "\nunique data Buffer where\n  MkBuffer : Bool -> Buffer\n\nshared : Buffer\n",
    ] {
        let error = refused(&format!("{preamble}{text}"));
        assert!(
            matches!(error, ElabError::OwnedTopLevel { .. }),
            "для {text:?} получено {error:?}"
        );
    }
    // Функция, **возвращающая** ресурс, законна: голова написанного типа -
    // стрелка, а связывания владеемого типа в ней нет.
    let text = format!("{preamble}\nopenIt : Bool -> File\nopenIt b = Open b\n");
    assert!(program(&text).lookup("openIt").is_some());
}

#[test]
fn a_resource_without_a_destructor_is_refused() {
    let text = format!("{BASE}\nresource File where\n  Open : Bool -> File\n");
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::ResourceWithoutDrop { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_field_with_ownership_requires_an_owning_type() {
    // Обёртка из обычного `data` отмывала бы владение: её связывания `ω`,
    // разбор идёт при `r = ω`, и поле кратности `1` приходит в ветвь как `ω` -
    // ресурс оказывается снаружи без линейности (§10 вопрос 70).
    let preamble = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
both : (1 x : Bool) -> (1 y : Bool) -> Bool
both x y = x
"
    );
    // Правило в одну фразу, обе половины которой - закрытые вопросы §10:
    // владеемое поле требует владеемого типа (70), ресурсное - ресурсного
    // (77). Второе о том, что уничтожение значения влечёт уничтожение полей, а
    // у `unique` деструктора нет и влечь ему нечем.
    for (name, source) in [
        (
            "обычный `data` с владеемым полем",
            "data Wrap where\n  MkWrap : File -> Wrap\n",
        ),
        (
            "`unique data` с ресурсным полем",
            "unique data Wrap where\n  MkWrap : File -> Wrap\n",
        ),
    ] {
        let error = refused(&format!("{preamble}\n{source}"));
        assert!(
            matches!(error, ElabError::OwnedField { .. }),
            "{name}: получено {error:?}"
        );
    }

    // `unique` поле у `unique` держателя законно: закрывать там нечего, а
    // линейность разбор сохраняет.
    let unique = format!(
        "{preamble}
unique data Buffer where
  MkBuffer : Bool -> Buffer

unique data Held where
  Hold : Buffer -> Held
"
    );
    assert!(program(&unique).lookup("Hold").is_some());

    // Обёртка над ресурсом остаётся выразимой - её объявляют `resource` со
    // своим деструктором, и тогда разбор идёт при `r = 1`, поле остаётся
    // линейным, а забытая обёртка закрывается.
    let wrapper = format!(
        "{preamble}
resource Wrap where
  MkWrap : File -> Wrap
  closeWrap : Wrap -> Bool
  closeWrap (MkWrap h) = drop h

closeOnce : Wrap -> Bool
closeOnce (MkWrap h) = drop h
"
    );
    assert!(program(&wrapper).lookup("closeOnce").is_some());
    let twice =
        format!("{wrapper}\ntwice : Wrap -> Bool\ntwice (MkWrap h) = both (drop h) (drop h)\n");
    assert!(
        matches!(refused(&twice), ElabError::Core { .. }),
        "линейное поле не расходуется дважды"
    );

    // И теперь она закрывается, будучи забытой: рекурсия §3.3 получила точку
    // входа, которой у `unique` не было.
    let forgotten = format!(
        "{wrapper}
openIt : Bool -> File
openIt b = Open b

leaked : Bool -> Bool
leaked b =
  let w : Wrap = MkWrap (openIt b)
  True
"
    );
    let signature = program(&forgotten);
    assert_eq!(
        calls(&signature, "leaked", "closeWrap"),
        1,
        "забытая обёртка зовёт свой деструктор"
    );
}

#[test]
fn a_lambda_does_not_capture_an_owned_binding() {
    // Замыкание переживает scope: вернув его, вызывающий получает ω-значение,
    // каждый вызов которого расходует один и тот же ресурс. Ядро этого не
    // видит - одноразовость применения в типе стрелки не записана.
    let preamble = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}"
    );
    let error = refused(&format!(
        "{preamble}\nmkCloser : File -> Bool -> Bool\nmkCloser h = \\x -> drop h\n"
    ));
    assert!(
        matches!(error, ElabError::ScopeBound { .. }),
        "получено {error:?}"
    );

    // Свой параметр захватом не является, и ресурс, которого лямбда не
    // касается, ей не мешает.
    let allowed = format!(
        "{preamble}
own : File -> Bool
own = \\h -> True

beside : File -> Bool -> Bool
beside h = \\b -> b
"
    );
    let signature = program(&allowed);
    assert_eq!(drops(&signature, "own"), 1, "свой параметр закрывается");
    assert_eq!(
        drops(&signature, "beside"),
        1,
        "чужой ресурс закрыт снаружи"
    );
}

#[test]
fn the_consumption_multiplicity_is_outside_conversion() {
    // `r` - учётная аннотация, а не часть вычисления: ι-редукция её не
    // смотрит, и два разбора, различающиеся только ею, дают одно значение.
    // Сравнивай их конвертируемость по `r` - и мотив, собранный при `r = 1`,
    // перестал бы совпадать с написанным при `r = ω`.
    let text = format!(
        "{BASE}
data P where
  MkP : Bool -> P

Q : Bool -> Type

fstOne : (1 p : P) -> Bool
fstOne (MkP b) = b

fstMany : P -> Bool
fstMany (MkP b) = b

same : (0 p : P) -> (1 x : Q (fstOne p)) -> Q (fstMany p)
same p x = x
"
    );
    assert!(program(&text).lookup("same").is_some());
}

#[test]
fn a_destructor_names_its_own_refusals() {
    // Оба случая раньше отвечали чужой причиной: голая сигнатура становилась
    // конструктором, и отказ приходил про отсутствующий `drop`, а второй
    // ресурсный тип получал от ядра «определение уже существует».
    let without_body = refused(&format!(
        "{BASE}\nresource File where\n  Open : Bool -> File\n  drop : File -> Bool\n"
    ));
    assert!(
        matches!(without_body, ElabError::DestructorWithoutBody { .. }),
        "получено {without_body:?}"
    );

    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
resource Socket where
  Conn : Bool -> Socket
  drop : Socket -> Bool
  drop (Conn b) = closeFile b
"
    );
    let shared = refused(&text);
    assert!(
        matches!(shared, ElabError::SharedDestructor { .. }),
        "получено {shared:?}"
    );
}

#[test]
fn a_destructor_that_cannot_close_is_refused() {
    // Вызов `drop` подставляет вставка, поэтому его форма - не вкус, а
    // условие работоспособности: лишний параметр превращает вставку в
    // частичное применение, владеемый результат заводит ресурс на каждом
    // закрытии, стёртый домен запрещает телу тронуть то, что оно закрывает.
    for drop in [
        "drop : File -> File\n  drop (Open b) = Open b",
        "drop : File -> Bool -> Bool\n  drop (Open b) c = b",
        "drop : (0 h : File) -> Bool\n  drop h = True",
        "drop : Bool -> Bool\n  drop b = b",
    ] {
        let text = format!("{BASE}\nresource File where\n  Open : Bool -> File\n  {drop}\n");
        let error = refused(&text);
        assert!(
            matches!(error, ElabError::DestructorShape { .. }),
            "для {drop:?} получено {error:?}"
        );
    }
}

#[test]
fn a_resource_body_defines_only_its_destructor() {
    // Тело держит конструкторы и **одно** определение - деструктор, каким бы
    // именем ни было названо. Второе определение - то, чему в теле не место:
    // пусти мы его туда, пришлось бы отвечать, видно ли снаружи имя, а это
    // пространства имён (§4.8, Фаза 3).
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

resource File where
  Open : Bool -> File
  close : File -> Bool
  close (Open b) = closeFile b
  helper : Bool -> Bool
  helper b = b
"
    );
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::ResourceMember { .. }),
        "получено {error:?}"
    );

    // Имя деструктора свободно: `drop` - соглашение §4.1, а не правило.
    let named = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

resource File where
  Open : Bool -> File
  close : File -> Bool
  close (Open b) = closeFile b

forgotten : File -> Bool
forgotten h = True
"
    );
    let signature = program(&named);
    assert_eq!(
        calls(&signature, "forgotten", "close"),
        1,
        "вставка зовёт деструктор по его собственному имени"
    );
}

/// Тело определения, напечатанное ядром: снимок формы, а не счёт подстрок.
fn body(signature: &Signature, name: &str) -> String {
    let Some(body) = signature.lookup(name).and_then(|it| it.body.clone()) else {
        panic!("у `{name}` есть тело")
    };
    body.to_string()
}

/// Сколько раз тело зовёт деструктор с этим именем.
fn calls(signature: &Signature, name: &str, destructor: &str) -> usize {
    body(signature, name).matches(destructor).count()
}

/// Сколько вызовов `drop` в теле определения.
fn drops(signature: &Signature, name: &str) -> usize {
    let Some(body) = signature.lookup(name).and_then(|it| it.body.clone()) else {
        panic!("у `{name}` есть тело")
    };
    body.to_string().matches("drop").count()
}

#[test]
fn a_resource_nobody_mentions_is_closed_automatically() {
    // §3.3: деструктор вызывается при выходе из scope. Правило решается на
    // исходнике - имя не встречается в теле, значит ресурс жив (§10 вопрос 71).
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
openIt : Bool -> File
openIt b = Open b

forgotten : Bool -> Bool
forgotten b =
  let h : File = openIt b
  True

closed : Bool -> Bool
closed b =
  let h : File = openIt b
  drop h

ignored : File -> Bool
ignored h = True

consumed : File -> Bool
consumed h = drop h
"
    );
    let signature = program(&text);
    assert_eq!(drops(&signature, "forgotten"), 1, "`let` без упоминания");
    assert_eq!(
        drops(&signature, "closed"),
        1,
        "написанный `drop` не удваивается"
    );
    assert_eq!(drops(&signature, "ignored"), 1, "аргумент без упоминания");
    assert_eq!(drops(&signature, "consumed"), 1, "аргумент израсходован");
}

#[test]
fn a_mention_in_an_erased_argument_is_not_a_use() {
    // Упоминание считается расходом только там, где расход есть: аргумент,
    // стоящий в `0`-параметре, ресурс не потребляет, и закрыть его обязана
    // сама функция. Кратности параметров написаны в сигнатуре - спрашивать
    // ядро (§10 вопросы 49а и 71) для этого не требуется.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
describe : (0 h : File) -> (1 b : Bool) -> Bool
consume : (1 h : File) -> Bool

erased : File -> Bool
erased h = describe h True

spent : File -> Bool
spent h = consume h

partly : File -> Bool
partly h = describe h (consume h)
"
    );
    let signature = program(&text);
    assert_eq!(
        drops(&signature, "erased"),
        1,
        "стёртый аргумент не расходует - ресурс закрывает вставка"
    );
    assert_eq!(
        drops(&signature, "spent"),
        0,
        "расходующий аргумент закрывает сам, вставке там делать нечего"
    );
    assert_eq!(
        drops(&signature, "partly"),
        0,
        "хватает одного расходующего вхождения"
    );
}

#[test]
fn a_shadowed_callee_does_not_lend_its_multiplicities() {
    // Голова применения даёт кратности, только если она то самое объявленное
    // имя. Затенённая локальная о них ничего не знает, и считать её аргумент
    // стёртым значило бы вставить `drop` к расходующему вызову - то есть
    // отвергнуть корректную программу.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
describe : (0 h : File) -> Bool

shadowing : (1 describe : File -> Bool) -> File -> Bool
shadowing describe h = describe h
"
    );
    let signature = program(&text);
    assert_eq!(
        drops(&signature, "shadowing"),
        0,
        "локальная голова расходует, как и всякая неизвестная"
    );
}

#[test]
fn a_shadowed_name_is_not_a_mention() {
    // Внутреннее связывание закрывает внешнее, и внешний ресурс остаётся
    // нетронутым - значит закрывается сам. Имя в теле при этом **есть**: не
    // будь оно затенено, вставка бы не сработала.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
shadowed : File -> Bool
shadowed h =
  let h : Bool = True
  h
"
    );
    let signature = program(&text);
    assert_eq!(drops(&signature, "shadowed"), 1);
}

#[test]
fn an_erased_owned_binding_is_not_closed() {
    // `drop` расходует ресурс, а стёртому связыванию расходовать нечем:
    // вставка отвергала бы корректную программу. §10 вопрос 71 обещает, что
    // лишний `drop` не вставляется никогда.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
openIt : Bool -> File
openIt b = Open b

quiet : (0 h : File) -> Bool
quiet h = True

bound : Bool -> Bool
bound b =
  let 0 h : File = openIt b
  True
"
    );
    let signature = program(&text);
    assert_eq!(drops(&signature, "quiet"), 0, "стёртый аргумент");
    assert_eq!(drops(&signature, "bound"), 0, "стёртое связывание");
}

#[test]
fn a_wildcard_and_a_lambda_close_like_a_named_argument() {
    // Три записи одного определения обязаны означать одно и то же: имя, `_` и
    // лямбда. У `_` имени нет вовсе, поэтому упоминанию взяться неоткуда, а у
    // лямбды тип виден по тому же спайну, из которого она берёт кратность.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
named : File -> Bool
named h = True

anonymous : File -> Bool
anonymous _ = True

viaLambda : File -> Bool
viaLambda = \\h -> True

viaWildcardLambda : File -> Bool
viaWildcardLambda = \\_ -> True
"
    );
    let signature = program(&text);
    for name in ["named", "anonymous", "viaLambda", "viaWildcardLambda"] {
        assert_eq!(drops(&signature, name), 1, "{name}");
    }
}

#[test]
fn closing_runs_at_the_end_of_the_scope_in_lifo_order() {
    // §3.3: деструктор зовётся при выходе из scope, порядок - LIFO. Форма
    // терма - предмет проверки: счёт вызовов её не видит, а разъехаться могут
    // именно порядок и индексы.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
openIt : Bool -> File
openIt b = Open b

lets : Bool -> Bool
lets b =
  let h : File = openIt b
      g : File = openIt b
  True

arguments : File -> File -> Bool
arguments h g = True
"
    );
    let signature = program(&text);
    insta::assert_snapshot!(format!(
        "lets = {}\n\narguments = {}",
        body(&signature, "lets"),
        body(&signature, "arguments")
    ));
}

#[test]
fn a_resource_field_is_closed_by_the_clause_that_took_it_apart() {
    // §3.3: уничтожение значения влечёт уничтожение его полей. Тип поля живёт
    // в объявлении конструктора, и оттуда же берётся его владение - поэтому
    // разобранное поле закрывается тем же правилом, что и аргумент.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
resource Wrapped where
  Wrap : File -> Wrapped
  closeWrapped : Wrapped -> Bool
  closeWrapped (Wrap h) = drop h

forgotten : Wrapped -> Bool
forgotten (Wrap h) = True

used : Wrapped -> Bool
used (Wrap h) = drop h

nested : Wrapped -> Bool
nested (Wrap (Open b)) = closeFile b
"
    );
    let signature = program(&text);
    assert_eq!(drops(&signature, "forgotten"), 1, "поле разобрано и забыто");
    assert_eq!(
        drops(&signature, "used"),
        1,
        "написанный `drop` не удваивается"
    );
    assert_eq!(
        drops(&signature, "nested"),
        0,
        "разобранный до конца ресурс закрывать нечего: полей ресурсного типа в нём нет"
    );
}

#[test]
fn a_closure_over_an_owned_binding_may_be_passed_but_not_returned() {
    // §3.3, scope-bound: захватившая лямбда применяется и передаётся
    // аргументом, но в позиции возвращаемого значения не появляется.
    let preamble = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
call : (1 k : Bool -> Bool) -> Bool
call k = k True

share : (ω k : Bool -> Bool) -> Bool
share k = k True
"
    );

    let signature = program(&format!(
        "{preamble}\npassed : File -> Bool\npassed h = call (\\b -> drop h)\n"
    ));
    assert!(
        signature.lookup("passed").is_some(),
        "аргументная позиция законна"
    );

    let escaped = refused(&format!(
        "{preamble}\nescaped : File -> (Bool -> Bool)\nescaped h = \\b -> drop h\n"
    ));
    assert!(
        matches!(escaped, ElabError::ScopeBound { .. }),
        "позиция возвращаемого значения - побег: {escaped:?}"
    );

    // ω-параметр ловит уже ядро, и отказ приходит на связывании: замыкание,
    // вызываемое сколько угодно раз, расходует один ресурс столько же.
    let shared = refused(&format!(
        "{preamble}\nwide : File -> Bool\nwide h = share (\\b -> drop h)\n"
    ));
    let Some(core) = shared.core() else {
        panic!("ожидался отказ ядра, получено {shared:?}");
    };
    assert!(
        matches!(core.kind, ErrorKind::UsageViolation { .. }),
        "получено {core:?}"
    );
}

#[test]
fn a_resource_wrapper_may_carry_a_captured_resource_out() {
    // §3.3 записывает это исключением и приводит `spawn`/`Task` собственным
    // примером: «захваченный ресурс покидает свой scope только внутри чего-то,
    // у чего есть деструктор». Проверялось же одно - конструктор ли голова, -
    // и `resource`-обёртка отвергалась наравне с обычной. Без исключения не
    // пишется вся документированная идиома переноса владения.
    let text = "\
data Bool where
  True : Bool

close : (1 b : Bool) -> Bool
close b = True

resource File where
  Open : Bool -> File
  shut : (1 h : File) -> Bool
  shut (Open b) = close b
";
    program(&format!(
        "{text}
resource Task where
  Spawned : (Bool -> Bool) -> Task
  cancel : (1 t : Task) -> Bool
  cancel (Spawned f) = True

spawn : (1 h : File) -> Task
spawn h = Spawned (\\b -> shut h)
"
    ));
    // У обычного `data` деструктора нет, и запрет остаётся: ровно та разница,
    // ради которой исключение и сформулировано.
    let error = refused(&format!(
        "{text}
data Holder where
  Held : (Bool -> Bool) -> Holder

leak : (1 h : File) -> Holder
leak h = Held (\\b -> shut h)
"
    ));
    assert!(error.to_string().contains("scope"), "получено {error:?}");
}

#[test]
fn being_scope_bound_travels_with_the_value_not_with_the_literal() {
    // §3.3 прямо говорит, что проверять позицию **литерала** недостаточно, и
    // показывает обход через `let`. Обходов на деле три, и все три об одном:
    // свойство принадлежит значению. Связывание перенимает его у значения,
    // конструктор уносит внутрь собранного, а функция, возвращающая свой
    // `1`-аргумент функционального типа, выносит наружу.
    let preamble = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
data Holder where
  Hold : (Bool -> Bool) -> Holder
"
    );

    for (name, source) in [
        (
            "поле конструктора",
            "stash : File -> Holder\nstash h = Hold (\\b -> drop h)\n",
        ),
        (
            "возврат через связывание",
            "sneaky : File -> (Bool -> Bool)\nsneaky h =\n  let 1 k : Bool -> Bool = \\b -> drop h\n  k\n",
        ),
        (
            "функция, возвращающая свой `1`-аргумент",
            "forward : (1 k : Bool -> Bool) -> (Bool -> Bool)\nforward k = k\n",
        ),
    ] {
        let error = refused(&format!("{preamble}\n{source}"));
        assert!(
            matches!(error, ElabError::ScopeBound { .. }),
            "{name}: получено {error:?}"
        );
    }

    // Применить - можно, в том числе через связывание и через оператор:
    // значение остаётся в своём scope, а сколько раз его позовут, считает
    // кратность, то есть ядро.
    let allowed = format!(
        "{preamble}
(<|) : (1 x : Bool) -> (1 k : Bool -> Bool) -> Bool
(<|) x k = k True

local : File -> Bool
local h =
  let 1 k : Bool -> Bool = \\b -> drop h
  k True

operand : File -> Bool
operand h = True <| (\\b -> drop h)
"
    );
    let signature = program(&allowed);
    for name in ["local", "operand"] {
        assert!(signature.lookup(name).is_some(), "{name}");
    }
}

#[test]
fn an_implicit_is_inserted_under_a_let() {
    // Дырка, заведённая под `let`, не вправе брать его связывание в спайн:
    // вычисление подставляет значение, и спайн перестаёт быть переменными, то
    // есть паттерном. В типе дырки связывание при этом остаётся - иначе
    // поехали бы индексы цели.
    let signature = program(&format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

identity : a -> a
identity x = x

f : Nat
f =
  let x : Nat = Succ Zero
  identity x
"
    ));
    let outcome = check_closed(
        &signature,
        &at("anything").apply([Term::constant("Succ").apply([Term::constant("Zero")])]),
        &at("P").apply([to("f")]),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn an_implicit_does_not_take_a_written_position() {
    // Правило вставки `drop` (§3.3) читает кратности параметров по спайну
    // объявленного типа, сопоставляя их с написанными аргументами. Имплисит
    // места в написанном не занимает: сочти его позицией - и `swallow h`
    // прочлось бы как расход в `0`-параметре, то есть «не упомянут», а `h`
    // закрылся бы вставкой сверх собственного расхода.
    //
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
consume : (1 x : a) -> (1 f : (1 y : a) -> Bool) -> Bool
consume x f = f x

release : (1 h : File) -> Bool
release h = consume h drop
"
    );
    program(&text);
}

#[test]
fn a_resource_does_not_instantiate_a_careless_parameter() {
    // §10 вопрос 76. Правило владения читает голову написанного типа, а под
    // переменной головы нет, и `swallow` принимает `File`, не закрывая его.
    // Ловит это кратность носителя: ядро посчитало, что значение типа `a`
    // употребляется в теле ноль раз, а владение требует ровно одного.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
swallow : (1 x : a) -> Bool
swallow x = True

release : (1 h : File) -> Bool
release h = swallow h
"
    );
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::OwnedCarrier { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_careless_parameter_is_inherited_from_whoever_was_called() {
    // Носители обязаны быть композиционны: `g` употребляет каждое своё
    // связывание ровно однажды и всё равно течёт, потому что течёт тот, кому
    // она их отдала. Без переноса чужого носителя на свою переменную дыра
    // открывается одним лишним слоем.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
swallow : (1 x : a) -> Bool
swallow x = True

g : (1 x : a) -> Bool
g x = swallow x

release : (1 h : File) -> Bool
release h = g h
"
    );
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::OwnedCarrier { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_family_parameter_makes_a_container() {
    // §10 вопрос 78. Параметр пишется слева от `:`, и тогда он не квантифицирует
    // конструктор, а значит и не поднимает универсум семейства. Проверяется не
    // форма, а то, что из неё следует: контейнер пишется и **вычисляет**.
    let signature = program(&format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

length : List a -> Nat
length Nil = Zero
length (Cons x xs) = Succ (length xs)

two : Nat
two = length (Cons True (Cons False Nil))
"
    ));
    let outcome = check_closed(
        &signature,
        &at("anything")
            .apply([Term::constant("Succ")
                .apply([Term::constant("Succ").apply([Term::constant("Zero")])])]),
        &at("P").apply([to("two")]),
    );
    assert!(outcome.is_ok(), "список из двух элементов: {outcome:?}");
}

#[test]
fn an_index_varies_where_a_parameter_stays() {
    // `Vect` из §4.1: `a` - параметр (одинаков во всех конструкторах), `n` -
    // индекс (меняется). Первое пишется слева от `:`, второе поднимается, и
    // тип его - `Nat`, а не `Type`: сказать это может только kind семейства.
    program(&format!(
        "{BASE}
data Vect (a : Type) : (0 n : Nat) -> Type where
  Nil : Vect a Zero
  Cons : a -> Vect a n -> Vect a (Succ n)

map : (a -> b) -> Vect a n -> Vect b n
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
"
    ));
}

#[test]
fn a_resource_needs_a_holder_that_closes_it() {
    // §3.3, вопрос 77: поле ресурсного типа требует держателя-`resource`.
    // Правило читало объявленный тип поля, а у `Cons : a -> …` головы нет -
    // инстанциация его обходила. С параметрами семейства обход стал
    // достижимым, и проверка переехала туда, где параметр получает значение.
    let text = format!(
        "{BASE}
closeFile : (1 b : Bool) -> Bool
closeFile b = b

{RESOURCE}
data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

files : List File
files = Nil
"
    );
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::OwnedHolder { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_case_expression_computes_what_it_says() {
    // §4.1: разбор выражением. Собирает его тот же компилятор, что и клаузы,
    // поэтому вложенные паттерны и «побеждает первая совпавшая» достаются
    // даром. Проверяется не форма терма, а то, что он **вычисляет**.
    let signature = program(&format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

pred : Nat -> Nat
pred n = case n of
  Zero -> Zero
  Succ k -> k
"
    ));
    for (input, output) in [(0, 0), (1, 0), (3, 2)] {
        let number = |value: u32| {
            (0..value).fold(Term::constant("Zero"), |term, _| {
                Term::constant("Succ").apply([term])
            })
        };
        let outcome = check_closed(
            &signature,
            &at("anything").apply([number(output)]),
            &at("P").apply([to("pred").apply([number(input)])]),
        );
        assert!(outcome.is_ok(), "pred {input} = {output}: {outcome:?}");
    }
}

#[test]
fn a_conditional_is_a_case_on_bool() {
    // `if` отдельного узла в ядре не имеет: он и есть разбор по `Bool`.
    // Отсюда и диагностика - про конструктор, а не про `if`.
    let signature = program(&format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

pick : Bool -> Nat
pick b = if b then Succ Zero else Zero
"
    ));
    let outcome = check_closed(
        &signature,
        &at("anything").apply([Term::constant("Succ").apply([Term::constant("Zero")])]),
        &at("P").apply([to("pick").apply([Term::constant("True")])]),
    );
    assert!(outcome.is_ok(), "{outcome:?}");

    let error = refused(&format!("{BASE}f : Nat -> Nat\nf x = if x then x else x\n"));
    assert!(
        matches!(error, ElabError::Clauses { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_case_under_a_binding_keeps_what_is_in_scope() {
    // Разбор поднимается в функцию от контекста и тут же к нему применяется,
    // поэтому связывания, видимые снаружи, видны и в ветвях - и кратности их
    // при подъёме сохраняются.
    program(&format!(
        "{BASE}
add : Nat -> Nat -> Nat
add Zero m = m
add (Succ k) m = Succ (add k m)

f : Nat -> Nat
f n =
  let m : Nat = Succ n
  case n of
    Zero -> m
    Succ k -> add k m
"
    ));
}

#[test]
fn a_case_reports_what_it_does_not_cover() {
    // Полнота приходит от того же компилятора, а колонка у разбора выражением
    // одна - разбираемое, - поэтому в примере стоит ровно то, что автор писал.
    let error = refused(&format!(
        "{BASE}f : Nat -> Bool\nf n = case n of\n  Zero -> True\n"
    ));
    let ElabError::Clauses { error, .. } = error else {
        panic!("ожидалась сборка клауз, получено {error:?}");
    };
    assert_eq!(error.to_string(), "не покрыто: `Succ _`");
}

#[test]
fn a_record_is_written_projected_and_punned() {
    // §4.2: тип записи, её значение, punning и проекция. Проверяется не форма
    // терма, а то, что запись **вычисляет**: `sum (mk 1 2)` сводится к трём.
    let signature = program(&format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

add : Nat -> Nat -> Nat
add Zero m = m
add (Succ k) m = Succ (add k m)

type Point = {{ x : Nat, y : Nat }}

mk : Nat -> Nat -> Point
mk x y = {{ x, y }}

sum : Point -> Nat
sum p = add p.x p.y
"
    ));
    let number = |value: u32| {
        (0..value).fold(Term::constant("Zero"), |term, _| {
            Term::constant("Succ").apply([term])
        })
    };
    let outcome = check_closed(
        &signature,
        &at("anything").apply([number(3)]),
        &at("P").apply([to("sum").apply([to("mk").apply([number(1), number(2)])])]),
    );
    assert!(outcome.is_ok(), "1 + 2 = 3 через запись: {outcome:?}");
}

#[test]
fn a_field_may_depend_on_an_earlier_one() {
    // `SomeVect` из §4.2: запись как первоклассный Σ-тип. Зависимость между
    // полями закрывает запись (решение 2026-08-29), и это её единственная цена.
    program(&format!(
        "{BASE}
data Vect (a : Type) : (0 n : Nat) -> Type where
  Nil : Vect a Zero
  Cons : a -> Vect a n -> Vect a (Succ n)

type Sized = {{ len : Nat, items : Vect Nat len }}

one : Sized
one = {{ len = Succ Zero, items = Cons Zero Nil }}

lengthOf : Sized -> Nat
lengthOf s = s.len
"
    ));
}

#[test]
fn a_record_declares_its_fields_or_assigns_them() {
    // Половина каждой формы не была бы ни тем ни другим: отказ приходит от
    // разбора, потому что решается это по написанию.
    assert!(parse("type Bad = { x : Nat, y = Zero }\n").is_err());
    // А написанное целиком одной формой - разбирается.
    assert!(parse("type Ok = { x : Nat, y : Nat }\n").is_ok());
    assert!(parse("p : Nat\np = { x = Zero, y }.x\n").is_ok());
}

#[test]
fn the_order_of_written_fields_does_not_matter() {
    // §4.2: ряд - набор меток, порядок в нём не значит ничего, и у значения
    // записи он инертен тем более. Сравнение же было позиционным с обеих
    // сторон: два написания одного ряда (`{y, z}` против `{z, y}`) не
    // сходились, и два значения одного типа - тоже.
    program(&format!(
        "{BASE}
two : {{ x : Nat | r }} -> {{ x : Nat | r }} -> Nat
two p q = Zero

rows : Nat
rows = two {{ x = Zero, y = Zero, z = Zero }} {{ x = Zero, z = Zero, y = Zero }}

type Point = {{ x : Nat, y : Nat }}

values : (0 f : Point -> Type) -> f {{ x = Zero, y = Succ Zero }} -> f {{ y = Succ Zero, x = Zero }}
values f v = v
"
    ));
}

#[test]
fn a_type_that_is_a_solved_hole_keeps_its_shape() {
    // Решённая дырка и есть своё решение, и всякий, кто смотрит на форму типа,
    // обязан видеть его, а не `?m`. Приведение к головной форме разворачивало
    // только глобальное имя, поэтому результат `identity` не был ни функцией,
    // ни записью: `(identity plus1) Zero` отвечало «ожидалась функция, получено
    // значение типа `(ω _ : Nat) -> Nat`» - печатая ровно ту форму, отсутствие
    // которой объявляло.
    program(&format!(
        "{BASE}
type Rec = {{ x : Nat }}

identity : a -> a
identity v = v

plus1 : Nat -> Nat
plus1 n = Succ n

r : Rec
r = {{ x = Zero }}

applied : Nat
applied = (identity plus1) Zero

projected : Nat
projected = (identity r).x
"
    ));
}

#[test]
fn a_dependent_record_is_closed() {
    // §4.2: зависимость закрывает запись, и auto-lift обязан это видеть.
    // Раздавая row-переменную всякой записи без написанного хвоста, он
    // открывал и `{ a : Type, b : a }`: лишнее поле проходило, а
    // `{ p | a = Bool }` подставляло чужое `a`, оставив прежнее `b`, - то есть
    // давало жителя любого типа. Сама подпись при этом законна: закрытой она и
    // задумана, отказом отвечает только лишнее поле.
    let signature = format!(
        "{BASE}
pick : {{ a : Type, b : a }} -> Nat
pick p = Zero
"
    );
    program(&format!(
        "{signature}\nfits : Nat\nfits = pick {{ a = Nat, b = Zero }}\n"
    ));
    let error = refused(&format!(
        "{signature}\nextra : Nat\nextra = pick {{ a = Nat, b = Zero, more = Zero }}\n"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );

    // Написанный хвост у зависимой записи - отказ, а не молчаливое сужение:
    // автор попросил открытую явно.
    let written = refused(&format!(
        "{BASE}
dep : {{ a : Type, b : a | r }} -> Nat
dep p = Zero
"
    ));
    assert!(
        matches!(
            written,
            ElabError::Core { ref error, .. }
                if matches!(error.kind, ErrorKind::OpenDependentRecord { .. })
        ),
        "получено {written:?}"
    );
}

#[test]
fn two_open_rows_of_different_depth_do_not_crash() {
    // Развёртка ряда считает тип `i`-го поля под своими `i` переменными, а
    // собираемый ряд стоит при исходном размере. На поле, ссылающемся на
    // предыдущее, глубины расходились, и обратное чтение упиралось в уровень,
    // которого при этом размере нет, - процесс падал. Отказ здесь и есть
    // ответ: §4.2 такой записи не разрешает, а ронять компилятор она не
    // вправе в любом случае.
    let error = refused(&format!(
        "{BASE}
apply1 : (({{ a : Type, b : a | r }}) -> Nat) -> Nat
apply1 f = Zero

fewer : {{ a : Type | s }} -> Nat
fewer p = Zero

got : Nat
got = apply1 fewer
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_record_passes_through_an_implicit() {
    // Значение записи против **дырки** (вставленного имплисита) идёт общим
    // путём: синтез даёт независимый тип, сравнение его же и решает. Без этого
    // всякая полиморфная функция над записью отказывала.
    program(&format!(
        "{BASE}
type Point = {{ x : Nat, y : Nat }}

identity : a -> a
identity v = v

p : Point
p = identity {{ x = Zero, y = Zero }}
"
    ));
}

#[test]
fn a_record_is_what_its_fields_are() {
    // η: `q` и `{x = q.x, y = q.y}` - одно значение. Проверяется тем, что
    // `anything q` подходит под `P (rebuild q)`: сойтись они могут только
    // через η, потому что `rebuild q` синтаксически другое.
    program(&format!(
        "{BASE}
type Point = {{ x : Nat, y : Nat }}

P : Point -> Type
anything : (0 q : Point) -> P q

rebuild : Point -> Point
rebuild q = {{ x = q.x, y = q.y }}

eta : (0 q : Point) -> P (rebuild q)
eta q = anything q
"
    ));
}

#[test]
fn a_projection_is_a_function_on_its_own() {
    // `.x` в позиции атома - сахар для `\p -> p.x` (§4.2). Примыкание решает,
    // что перед чем: `map .x` есть применение, `p.x` - проекция.
    program(&format!(
        "{BASE}
type Point = {{ x : Nat, y : Nat }}

apply : (Point -> Nat) -> Point -> Nat
apply f p = f p

n : Nat
n = apply .x {{ x = Succ Zero, y = Zero }}
"
    ));
}

#[test]
fn a_record_in_a_signature_takes_extra_fields() {
    // §4.2, auto-lift: `{ x : Nat, y : Nat } -> Nat` элаборируется в
    // `{0 r : Row} -> { x : Nat, y : Nat | r } -> Nat`, поэтому работает и на
    // записи с лишним полем. Row-переменную автор не пишет.
    program(&format!(
        "{BASE}
first : {{ x : Nat, y : Nat }} -> Nat
first p = p.x

flat : Nat
flat = first {{ x = Zero, y = Zero }}

wide : Nat
wide = first {{ x = Zero, y = Zero, z = Succ Zero }}
"
    ));
}

#[test]
fn open_records_compose() {
    // Открытая запись, переданная дальше, - самый обычный код, и до правки
    // 2026-08-30 он не проходил: два открытых ряда сводились через свежий
    // остаток, дырку под который нечем было типизировать. Остаток теперь
    // выражается хвостом той стороны, которой нечего добавить.
    program(&format!(
        "{BASE}
first : {{ x : Nat, y : Nat }} -> Nat
first p = p.x

again : {{ x : Nat, y : Nat }} -> Nat
again q = first q

wider : {{ x : Nat, y : Nat, z : Nat }} -> Nat
wider q = first q

counted : {{ x : Nat, y : Nat }} -> Nat -> Nat
counted p Zero = p.x
counted p (Succ k) = counted p k
"
    ));
}

#[test]
fn one_written_record_gives_one_row_variable() {
    // Группа `(0 a b : …)` элаборирует свой тип по разу на имя, и раздача по
    // счётчику уезжала: `b` получала закрытую запись молча. Написан тип один -
    // значит и переменная одна. Соседняя запись при этом своя: два разных
    // параметра расширяются независимо.
    program(&format!(
        "{BASE}
pair : (0 a b : {{ x : Nat, y : Nat }}) -> Nat
pair a b = Zero

both : Nat
both = pair {{ x = Zero, y = Zero, z = Zero }} {{ x = Zero, y = Zero, z = Zero }}

apart : {{ x : Nat, y : Nat }} -> {{ a : Nat, b : Nat }} -> Nat
apart p q = p.x

mixed : Nat
mixed = apart {{ x = Zero, y = Zero, z = Zero }} {{ a = Zero, b = Zero }}
"
    ));
}

#[test]
fn an_open_record_does_not_gain_fields_it_lacks() {
    // Обратное направление обязано отказывать: `wide` требует `z`, а у
    // открытой записи с `x` и `y` его нет и взяться неоткуда - хвост
    // принадлежит вызывающему, не вызываемому.
    let error = refused(&format!(
        "{BASE}
wide : {{ x : Nat, y : Nat, z : Nat }} -> Nat
wide q = q.z

narrow : {{ x : Nat, y : Nat }} -> Nat
narrow p = wide p
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_record_alias_is_closed() {
    // Запись в алиасе `type` закрыта (§4.2): `Point` - конкретный тип, а не
    // «класс записей, содержащих x и y». Лишнее поле поэтому не подходит.
    let error = refused(&format!(
        "{BASE}
type Point = {{ x : Nat }}

p : Point
p = {{ x = Zero, y = Zero }}
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn an_update_and_an_extension_are_one_form() {
    // §4.2: `{ p | field = value }` - и обновление, и расширение. Различает их
    // тип исходной записи, а не автор. Проверяется вычислением: обновлённое
    // поле изменилось, соседнее осталось.
    let signature = program(&format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

type Point = {{ x : Nat, y : Nat }}
type Point3D = {{ x : Nat, y : Nat, z : Nat }}

moved : Point -> Point
moved p = {{ p | x = Succ p.x }}

promote : Point -> Nat -> Point3D
promote p z = {{ p | z = z }}

start : Point
start = {{ x = Zero, y = Succ Zero }}
"
    ));
    let number = |value: u32| {
        (0..value).fold(Term::constant("Zero"), |term, _| {
            Term::constant("Succ").apply([term])
        })
    };
    // `(moved start).x` есть `1`, а `.y` осталось `1`.
    for (field, expected) in [("x", 1), ("y", 1)] {
        let projected = Term::Project(Rc::new(to("moved").apply([to("start")])), field.into());
        let outcome = check_closed(
            &signature,
            &at("anything").apply([number(expected)]),
            &at("P").apply([projected]),
        );
        assert!(outcome.is_ok(), "поле {field}: {outcome:?}");
    }
    // Расширение дописывает поле, не трогая прежние.
    let promoted = to("promote").apply([to("start"), number(2)]);
    let outcome = check_closed(
        &signature,
        &at("anything").apply([number(2)]),
        &at("P").apply([Term::Project(Rc::new(promoted), "z".into())]),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn an_open_record_is_updated_in_place() {
    // Пересборка перечисляет поля, а у записи с хвостом их знает только хвост,
    // поэтому переопределение уходит в ядро формой `With`. Хвост при этом
    // сохраняется - и потому сигнатура пишет его явно (§4.2).
    program(&format!(
        "{BASE}
shift : {{ x : Nat, y : Nat | r }} -> {{ x : Nat, y : Nat | r }}
shift p = {{ p | x = Succ p.x }}

moved : Nat
moved = (shift {{ x = Zero, y = Zero, z = Zero }}).x

kept : Nat
kept = (shift {{ x = Zero, y = Zero, z = Succ Zero }}).z
"
    ));
}

#[test]
fn an_open_record_gains_a_field() {
    // Та же форма - расширение: метки нет у базы, значит она дописывается.
    // Различает их тип базы, а не автор (§4.2).
    program(&format!(
        "{BASE}
tag : {{ x : Nat | r }} -> {{ x : Nat, ok : Bool | r }}
tag p = {{ p | ok = True }}

added : Bool
added = (tag {{ x = Zero, y = Zero }}).ok

carried : Nat
carried = (tag {{ x = Zero, y = Succ Zero }}).y
"
    ));
}

#[test]
fn a_record_in_a_result_is_closed() {
    // Подъём идёт только в отрицательных позициях (§4.2, решение 2026-08-29).
    // До правки `mk : Nat -> { x : Nat }` был необитаем: квантор по хвосту
    // требовал произвести поля, которых автор не знает.
    program(&format!(
        "{BASE}
mk : Nat -> {{ x : Nat }}
mk n = {{ x = n }}

got : Nat
got = (mk Zero).x
"
    ));
}

#[test]
fn a_record_under_two_arrows_is_closed_again() {
    // Полярность считается по стрелкам, а не по глубине: у `run` аргумент -
    // функция, и её собственный аргумент оказывается в положительной позиции.
    // Значит `f` принимает ровно `{ x : Nat }`, и лишнее поле ему не отдать.
    let error = refused(&format!(
        "{BASE}
run : ({{ x : Nat, y : Nat }} -> Nat) -> Nat
run f = f {{ x = Zero, y = Zero, z = Zero }}
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_written_tail_preserves_fields() {
    // Функция, сохраняющая поля, пишет хвост явно - так же, как §4.11. Имя
    // хвоста поднимается как `Row ℓ`, одно на обе записи, и лишнее поле
    // проходит насквозь.
    program(&format!(
        "{BASE}
keep : {{ x : Nat | r }} -> {{ x : Nat | r }}
keep p = p

why : {{ y : Nat, z : Nat }} -> Nat
why q = q.y

through : Nat
through = why (keep {{ x = Zero, y = Succ Zero, z = Zero }})

direct : Nat
direct = (keep {{ x = Zero, y = Succ Zero }}).y

type Both = {{ x : Nat, y : Nat }}

closed : Both
closed = keep {{ x = Zero, y = Zero }}
"
    ));
}

#[test]
fn a_written_tail_needs_a_binder() {
    // Хвост только ссылается: связывания он не создаёт. В алиасе `type`
    // поднимать некому, и молча потерять хвост нельзя - это сузило бы
    // написанный тип.
    let error = refused(&format!(
        "{BASE}
type Wide = {{ x : Nat | r }}
"
    ));
    assert!(
        matches!(error, ElabError::UnknownName { .. }),
        "получено {error:?}"
    );
}

#[test]
fn an_implicit_binder_group_is_written() {
    // §4.1: `{0 a : Type}` пишется руками, а не только поднимается из
    // свободного имени. Вставка аргумента в месте использования - та же, что у
    // поднятого: видимость у `Pi` одна, откуда она взялась, дальше неважно.
    let signature = program(&format!(
        "{BASE}
identity : {{0 a : Type}} -> a -> a
identity x = x

b : Bool
b = identity True

n : Nat
n = identity Zero

written : Bool
written = identity @Bool False
"
    ));
    assert!(signature.lookup("identity").is_some());
}

#[test]
fn an_implicit_binder_group_stands_anywhere_in_the_telescope() {
    // Имплисит между явными параметрами - не особый случай: клауза
    // раздаёт паттерны по видимым связываниям, а на невидимые ставит `_`.
    program(&format!(
        "{BASE}
first : Nat -> {{0 a : Type}} -> a -> Nat
first n x = n

got : Nat
got = first Zero True
"
    ));
}

#[test]
fn a_group_of_names_shares_its_type_and_visibility() {
    // Группа `{0 a b : Type}` разворачивается в два связывания, и оба
    // выводимые. Тип элаборируется заново под каждым именем, но в области
    // видимости, где имён группы ещё нет.
    program(&format!(
        "{BASE}
apply : {{0 a b : Type}} -> (a -> b) -> a -> b
apply f x = f x

double : Nat -> Nat
double n = Succ (Succ n)

used : Nat
used = apply double Zero
"
    ));
}

#[test]
fn a_written_implicit_keeps_the_default_multiplicity() {
    // Умолчание у фигурной группы то же, что у круглой, - `ω` (§4.1).
    // Подъём свободного имени даёт `0`, и это расхождение намеренное:
    // написанная группа - способ попросить имплисит, доживающий до рантайма.
    // Здесь оно видно прямо: `n` уходит в `ω`-позицию.
    program(&format!(
        "{BASE}
tagged : {{n : Nat}} -> Bool -> Nat
tagged b = n

got : Nat
got = tagged @(Succ Zero) True
"
    ));
}

#[test]
fn an_erased_implicit_does_not_reach_the_body() {
    // Зеркало предыдущего: при `0` то же тело отвергается - стёртое
    // связывание в рантайм-позиции.
    let error = refused(&format!(
        "{BASE}
tagged : {{0 n : Nat}} -> Bool -> Nat
tagged b = n
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn an_inserted_argument_costs_what_a_written_one_costs() {
    // Проверка до финальных ворот смотрела на терм с дырками, а дырка инертна:
    // ничего не расходует. Поэтому `pair2 k (len v)` при `(1 k : Nat)`
    // принималось, а `pair2 k (len @k v)` - тот же аргумент, написанный рукой -
    // отвергалось. Кто вписал аргумент, к §3.1 отношения не имеет: обе формы
    // расходуют `k` дважды, и обе обязаны быть отказом.
    let inserted = format!(
        "{BASE}
data Vect : Nat -> Type where
  Nil : Vect Zero
  Cons : (0 n : Nat) -> Nat -> Vect n -> Vect (Succ n)

pair2 : (1 x : Nat) -> (1 y : Nat) -> Nat
pair2 x y = x

len : {{n : Nat}} -> Vect n -> Nat
len v = Zero

sneaky : (1 k : Nat) -> Vect k -> Nat
sneaky k v = pair2 k (len v)
"
    );
    let written = inserted.replace("len v)", "len @k v)");
    assert!(
        matches!(refused(&inserted), ElabError::Core { .. }),
        "вставленный аргумент обязан расходовать"
    );
    assert!(
        matches!(refused(&written), ElabError::Core { .. }),
        "написанный аргумент расходовал всегда"
    );
}

#[test]
fn a_parameter_of_a_family_is_erased() {
    // §10 вопрос 78: параметр семейства в значении не хранится, поэтому
    // конструктор берёт его стёртым - как поднятое имя берёт `{0 a : Type}`
    // (§4.1). Умолчание `ω` лишило бы язык всякого полиморфного конструктора:
    // `Wrap y` при `{0 b : Type}` расходовало бы стёртую переменную. Обе формы
    // - и вставленная, и написанная - проверяются вместе: разойдись они, это и
    // был бы дефект, который ворота ловят.
    let inserted = format!(
        "{BASE}
data Box a where
  Wrap : a -> Box a

plain : {{0 b : Type}} -> b -> Box b
plain y = Wrap y
"
    );
    program(&inserted);
    program(&inserted.replace("Wrap y\n", "Wrap @b y\n"));
}

#[test]
fn a_single_field_record_in_a_domain_reads_as_a_binder_group() {
    // §10 вопрос 79: `{ x : Nat } -> Nat` читается и как группа связываний, и
    // как тип записи. Побеждает связывание (решение 2026-08-29), а запись в
    // домене пишет хвост явно - в домене она всё равно открыта, поэтому формы
    // эквивалентны. Здесь `x` связано и видно в кодомене.
    program(&format!(
        "{BASE}
depends : {{x : Nat}} -> Bool -> Nat
depends b = x

got : Nat
got = depends @Zero True

record : {{ x : Nat | r }} -> Nat
record p = p.x

wide : Nat
wide = record {{ x = Zero, y = Zero }}
"
    ));
}

#[test]
fn a_module_is_a_record_of_its_members() {
    // §4.8: члены поднимаются на верхний уровень под квалифицированными
    // именами, а модуль объявляется записью из них. Доступ - проекция, и
    // потому `NatEq.T` в позиции типа работает тем же правилом, что и
    // `NatEq.zero` в позиции терма.
    program(&format!(
        "{BASE}
module NatEq where
  type T = Nat
  zero : T
  zero = Zero

typed : NatEq.T
typed = NatEq.zero
"
    ));
}

#[test]
fn a_member_sees_its_neighbours_and_itself() {
    // Короткое имя внутри тела - ссылка на соседа: `eq` находит `T`, а
    // рекурсивный вызов находит себя. Оба - следствие подъёма: определение
    // объявлено как `NatEq.eq`, и найти его надо по написанному `eq`.
    program(&format!(
        "{BASE}
module NatEq where
  type T = Nat
  eq : T -> T -> Bool
  eq Zero Zero = True
  eq (Succ a) (Succ b) = eq a b
  eq a b = False

answer : Bool
answer = NatEq.eq (Succ Zero) (Succ Zero)
"
    ));
}

#[test]
fn a_module_signature_is_a_record_type() {
    // `module type` объявляет тип записи, а члены её - телескоп: `eq` видит
    // `T`. Абстрактный типовой член - поле сорта `Type`, и какой универсум
    // ему достанется, решает тот, кто сигнатуру реализует.
    program(&format!(
        "{BASE}
module type Eqv where
  type T
  eq : T -> T -> Bool

module NatEq : Eqv where
  type T = Nat
  eq : T -> T -> Bool
  eq a b = True
"
    ));
}

#[test]
fn a_module_must_satisfy_its_ascription() {
    // Аннотация - обязательство: член сигнатуры, которого нет в модуле,
    // отвергается той же проверкой, что и всякое тело против типа.
    let error = refused(&format!(
        "{BASE}
module type Eqv where
  type T
  eq : T -> T -> Bool

module Broken : Eqv where
  type T = Nat
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn modules_nest() {
    // Вложенность даётся квалификацией: член внутреннего модуля объявлен как
    // `Outer.Inner.flag`, сам внутренний - поле внешнего. Отдельного правила
    // для этого нет.
    program(&format!(
        "{BASE}
module Outer where
  module Inner where
    flag : Bool
    flag = True

used : Bool
used = Outer.Inner.flag
"
    ));
}

#[test]
fn an_abstract_type_member_belongs_to_a_signature() {
    // `type T` без уравнения объявляет член сигнатуры модуля; снаружи неё тип
    // брать неоткуда, а постулировать имя можно обычной сигнатурой.
    let error = refused(&format!("{BASE}type T\n"));
    assert!(
        matches!(error, ElabError::AbstractType { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_signature_carries_no_implementations() {
    // Клаузы в `module type` и семейство в теле модуля - две названные
    // границы. Первая - от смысла сигнатуры, вторая от того, что имена
    // конструкторов пока не квалифицируются.
    for text in [
        "module type Eqv where\n  eq : Bool\n  eq = True\n",
        "module M where\n  data Tree where\n    Leaf : Tree\n",
    ] {
        let error = refused(&format!("{BASE}{text}"));
        assert!(
            matches!(error, ElabError::ModuleMember { .. }),
            "для {text:?} получено {error:?}"
        );
    }
}

#[test]
fn sealing_hides_the_representation() {
    // §3.5: `:` проверяет, `:>` проверяет и запечатывает. Запечатанное
    // определение ядро не разворачивает, поэтому `Sealed.T` снаружи - атом, а
    // не `Nat`, и значение своего представления под него не подходит.
    let text = "
module type Counter where
  type T
  start : T

module Clear : Counter where
  type T = Nat
  start : T
  start = Zero

module Hidden :> Counter where
  type T = Nat
  start : T
  start = Zero
";
    // Незапечатанный прозрачен: представление видно, и `Zero` подходит.
    program(&format!(
        "{BASE}{text}
seen : Clear.T
seen = Zero
"
    ));
    // Запечатанный - нет, и пользоваться им можно только через его же члены.
    program(&format!(
        "{BASE}{text}
carried : Hidden.T
carried = Hidden.start
"
    ));
    let error = refused(&format!(
        "{BASE}{text}
leaked : Hidden.T
leaked = Zero
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_signature_takes_no_ascription() {
    // Аннотация проверяет модуль против интерфейса, а сигнатура интерфейсом и
    // является. Уточнение сигнатуры - отдельная операция, и её пока нет.
    let error = refused(&format!(
        "{BASE}
module type A where
  flag : Bool

module type B : A where
  flag : Bool
"
    ));
    assert!(
        matches!(error, ElabError::ModuleMember { .. }),
        "получено {error:?}"
    );
}

/// Сигнатура и её реализация - основа примеров про функторы.
const EQV: &str = "
module type Eqv where
  type T
  eq : T -> T -> Bool

module NatEq : Eqv where
  type T = Nat
  eq : T -> T -> Bool
  eq a b = True
";

#[test]
fn a_functor_takes_a_module() {
    // §4.8: функтор - модуль, параметризованный модулем, а применение его -
    // обычный вызов. Член поднят вместе с параметром, поэтому написанное
    // внутри `drain` есть `Counting.drain Key` - специализированный член, и
    // рекурсия внутри функтора работает тем же правилом, что и снаружи.
    program(&format!(
        "{BASE}{EQV}
module Counting (Key : Eqv) where
  type Item = Key.T
  drain : Nat -> Item -> Nat
  drain Zero x = Zero
  drain (Succ k) x = drain k x

module NatCounting = Counting NatEq

used : Nat
used = NatCounting.drain (Succ Zero) Zero
"
    ));
}

#[test]
fn a_functor_argument_is_checked() {
    // Параметр несёт сигнатуру, и модуль, ей не удовлетворяющий, отвергается
    // там же, где написан - применение функтора есть обычное применение.
    let error = refused(&format!(
        "{BASE}{EQV}
module Empty where
  flag : Bool
  flag = True

module Broken = Counting Empty

module Counting (Key : Eqv) where
  same : Key.T -> Bool
  same a = True
"
    ));
    assert!(
        matches!(
            error,
            ElabError::Core { .. } | ElabError::UnknownName { .. }
        ),
        "получено {error:?}"
    );
}

#[test]
fn a_functor_applied_twice_gives_one_type() {
    // §4.8: аппликативность «получена даром» - и не была получена. Разворот
    // определения переигрывал спайн только над записью, а у модуля,
    // объявленного выражением, тело - нейтраль: проекция на ней не бралась,
    // и `None` отбрасывал уже сделанный δ-шаг вместе с ней. `M.T` не
    // разворачивалась вовсе, поэтому два применения функтора к одному
    // аргументу давали неконвертируемые типы, а `module A = NatEq` был
    // непрозрачен без всякого `:>`.
    program(&format!(
        "{BASE}{EQV}
module Plain (Key : Eqv) where
  type T = Key.T

module G1 = Plain NatEq
module G2 = Plain NatEq

conv : G1.T -> G2.T
conv x = x

toNat : G1.T -> Nat
toNat x = x

module A1 = NatEq

alias : A1.T -> Nat
alias x = x
"
    ));
}

#[test]
fn sealing_reaches_a_nested_module() {
    // Флаг непрозрачности ставился только непосредственным членам, а вложенный
    // модуль поднимает свои под своей квалификацией: `Outer.Inner.Flag`
    // оставался прозрачным. На одном уровне `:>` держал, на двух - нет.
    let error = refused(&format!(
        "{BASE}
module type InnerSig where
  type Flag

module type OuterSig where
  Inner : InnerSig

module Outer :> OuterSig where
  module Inner where
    type Flag = Bool

leak : Outer.Inner.Flag
leak = True
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn the_sealing_rule_reaches_a_signature_inside_a_module() {
    // Нарушение записывалось под квалифицированным именем сигнатуры, а
    // спрашивалось по написанному тексту аннотации: клалось `Outer.BagSig`,
    // искалось `BagSig`, и `module type` внутри модуля обходил правило
    // целиком. Спрашиваются теперь обе формы - и короткая, и квалифицированная.
    let error = refused(&format!(
        "{BASE}
class Eqv a where
  eq : a -> a -> Bool

module Outer where
  module type BagSig where
    type Bag (a : Type)
    empty : {{a : Type}} -> Bag a
    add : {{a : Type}} -> {{Eqv a}} => a -> Bag a -> Bag a

  module Sealed :> BagSig where
    type Bag (a : Type) = Nat
    empty : {{a : Type}} -> Nat
    empty = Zero
    add : {{a : Type}} -> {{Eqv a}} => a -> Nat -> Nat
    add x b = b
"
    ));
    assert!(
        matches!(error, ElabError::SealedConstraint { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_sealed_functor_hides_its_result() {
    // §3.5: аппликативность - следствие, а не отдельное решение. `Hidden.T`
    // разворачивается в проекцию от применения, а `Dup` запечатан, поэтому
    // вычисление застревает и представление наружу не выходит.
    let text = format!(
        "{BASE}{EQV}
module Dup (Key : Eqv) :> Eqv where
  type T = Key.T
  eq : T -> T -> Bool
  eq a b = Key.eq a b

module Hidden = Dup NatEq
"
    );
    program(&format!(
        "{text}
kept : Bool
kept = True
"
    ));
    let error = refused(&format!(
        "{text}
leaked : Hidden.T
leaked = Zero
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_signature_takes_no_parameters() {
    // Параметр делает функцию от интерфейса, а сигнатура интерфейсом и
    // является. То же и с вложенностью внутри функтора: члены внутреннего
    // модуля поднялись бы со своими параметрами, а внешние им тоже нужны.
    for text in [
        "module type Bad (Key : Eqv) where\n  flag : Bool\n",
        "module Outer (Key : Eqv) where\n  module Inner where\n    flag : Bool\n    flag = True\n",
    ] {
        let error = refused(&format!("{BASE}{EQV}{text}"));
        assert!(
            matches!(error, ElabError::ModuleMember { .. }),
            "для {text:?} получено {error:?}"
        );
    }
}

/// Класс с одним методом и инстанс на `Nat` - основа примеров про разрешение.
const EQ_CLASS: &str = "
class Eqv a where
  eq : a -> a -> Bool

instance Eqv Nat where
  eq Zero Zero = True
  eq (Succ a) (Succ b) = eq a b
  eq a b = False
";

#[test]
fn a_method_resolves_by_the_type_of_its_argument() {
    // §3.5: класс есть module type плюс режим разрешения. Словарь вставляется
    // дыркой и заполняется поиском, когда проверка уже решила `a := Nat`;
    // энергично его не вставить - тип в момент вставки ещё неизвестен.
    program(&format!(
        "{BASE}{EQ_CLASS}
instance Eqv Bool where
  eq a b = True

counted : Bool
counted = eq (Succ Zero) (Succ Zero)

flagged : Bool
flagged = eq True False
"
    ));
}

#[test]
fn a_method_computes_through_the_dictionary() {
    // Словарь - обычная запись, метод - обычная проекция, поэтому вызов
    // **вычисляется**: `Wit (eq Zero Zero)` принимает `Yes : Wit True` только
    // если разворот дошёл до `True`.
    program(&format!(
        "{BASE}{EQ_CLASS}
data Wit : Bool -> Type where
  Yes : Wit True

witnessed : Wit (eq Zero Zero)
witnessed = Yes
"
    ));
}

#[test]
fn a_missing_instance_names_the_type() {
    // Поиск - управляющий поток, и окончательный отказ называет и класс, и тип.
    let error = refused(&format!(
        "{BASE}{EQ_CLASS}
data Unit where
  It : Unit

missing : Bool
missing = eq It It
"
    ));
    assert!(
        matches!(error, ElabError::NoInstance { .. }),
        "получено {error:?}"
    );
}

#[test]
fn one_instance_per_type_and_class() {
    // Два инстанса на один тип - неоднозначность, и разрешать её пока нечем:
    // именованных инстансов и `using` в языке нет.
    let error = refused(&format!(
        "{BASE}{EQ_CLASS}
instance Eqv Nat where
  eq a b = False
"
    ));
    assert!(
        matches!(error, ElabError::ModuleMember { .. }),
        "получено {error:?}"
    );
}

#[test]
fn an_instance_carries_only_clauses() {
    // Тип метода написан в классе, поэтому инстанс его не переписывает - и
    // не вправе: две записи одного типа разъезжались бы молча.
    let error = refused(&format!(
        "{BASE}{EQ_CLASS}
instance Eqv Bool where
  eq : Bool -> Bool -> Bool
  eq a b = True
"
    ));
    assert!(
        matches!(error, ElabError::ModuleMember { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_constraint_is_written_and_resolved_from_the_context() {
    // §4.1: `{Eqv a} =>` есть группа implicit-связываний, у которой аргумент
    // заполняется поиском, а не унификацией. Внутри тела голова цели -
    // переменная, инстанса для неё нет и быть не может, поэтому словарь
    // берётся из контекста: он и есть тот, о котором договорилась сигнатура.
    program(&format!(
        "{BASE}{EQ_CLASS}
same : {{Eqv a}} => a -> a -> Bool
same x y = eq x y

both : {{Eqv a, Eqv b}} => a -> b -> Bool
both x y = eq x x

data Wit : Bool -> Type where
  Yes : Wit True

used : Wit (same Zero Zero)
used = Yes
"
    ));
}

#[test]
fn a_constraint_without_an_instance_is_refused() {
    // Полиморфная функция без констрейнта словарь взять неоткуда: ни
    // контекста, ни инстанса для переменной.
    let error = refused(&format!(
        "{BASE}{EQ_CLASS}
loose : a -> a -> Bool
loose x y = eq x y
"
    ));
    assert!(
        matches!(error, ElabError::NoInstance { .. }),
        "получено {error:?}"
    );
}

#[test]
fn an_instance_may_have_a_context() {
    // §3.5: инстанс с контекстом - не значение, а функция от словарей.
    // Разрешение поэтому применяет кандидата к дыркам, а словарь его
    // контекста возвращается в ту же очередь и решается следующим шагом -
    // рекурсия поиска получается из цикла, а не из отдельного обхода.
    program(&format!(
        "{BASE}{EQ_CLASS}
data Box a where
  Wrap : a -> Box a

instance {{Eqv a}} => Eqv (Box a) where
  eq (Wrap x) q = eq x x

used : Bool
used = eq (Wrap Zero) (Wrap Zero)
"
    ));
}

#[test]
fn a_context_dictionary_is_not_an_instance_for_the_variable() {
    // Инстанса на `Box a` нет, а контекст говорит только про `a`: цель
    // `Eqv (Box a)` внутри такого тела не решается ничем.
    let error = refused(&format!(
        "{BASE}{EQ_CLASS}
data Box a where
  Wrap : a -> Box a

wrong : {{Eqv a}} => Box a -> Bool
wrong p = eq p p
"
    ));
    assert!(
        matches!(error, ElabError::NoInstance { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_pattern_variable_takes_the_type_of_its_own_binding() {
    // Домен связывания, взятый термом, записан на глубине своего места в
    // телескопе, а связывается на глубине числа уже связанных переменных.
    // Совпадают они, только пока каждый аргумент даёт ровно одну переменную;
    // здесь `y` получал тип чужого связывания (лог 2026-08-31).
    program(&format!(
        "{BASE}
data Box a where
  Wrap : a -> Box a

second : {{0 a : Type}} -> {{0 b : Type}} -> Box a -> Box b -> Box b
second (Wrap x) (Wrap y) = Wrap y
"
    ));
}

#[test]
fn an_instance_context_carries_recursion() {
    // Канонический случай §3.5: инстанс на списке зовёт себя на хвосте и
    // словарь контекста на элементе. Оба имени - одно и то же `eq`, и
    // различает их только тип аргумента.
    program(&format!(
        "{BASE}{EQ_CLASS}
data List a where
  Nil : List a
  Cons : a -> List a -> List a

instance {{Eqv a}} => Eqv (List a) where
  eq Nil Nil = True
  eq (Cons x xs) (Cons y ys) = eq xs ys
  eq p q = False

answer : Bool
answer = eq (Cons Zero Nil) (Cons Zero Nil)
"
    ));
}

#[test]
fn an_instance_context_that_does_not_shrink_is_refused() {
    // Разрешение рекурсивно по построению (§3.5), а убывания цели форма
    // инстанса не обещает: `Eqv (Box a)` в контексте у `Eqv (Box a)` -
    // законная запись, ведущая в саму себя. Без предела глубины она съедает
    // память вместо ответа, поэтому проверяется именно отказ, а не «не упало».
    let error = refused(&format!(
        "{BASE}{EQ_CLASS}
data Box a where
  Wrap : a -> Box a

instance {{Eqv (Box a)}} => Eqv (Box a) where
  eq p q = True

answer : Bool
answer = eq (Wrap Zero) (Wrap Zero)
"
    ));
    assert!(
        matches!(error, ElabError::InstanceDepth { .. }),
        "ожидался предел глубины, получено: {error}"
    );
}

#[test]
fn the_dictionary_of_the_declared_instance_carries_its_superclasses() {
    // Член инстанса вправе потребовать словарь **своего же** инстанса: имени у
    // того ещё нет, и словарь собирается записью из членов. Запись эта обязана
    // нести и поля суперклассов - иначе первая же их проекция роняет `eval`, а
    // без проекции неполный словарь молча уезжает в сигнатуру.
    program(&format!(
        "{BASE}{EQ_CLASS}
class Ord a when Eqv a where
  cmp : a -> a -> Bool

both : {{Ord a}} => a -> a -> Bool
both x y = eq x y

instance Ord Nat where
  cmp x y = both x y
"
    ));
}

#[test]
fn a_goal_of_another_shape_is_not_the_declared_instance() {
    // Головы аргументов у `Eqv (List a)` и `Eqv (List Nat)` одни и те же, а
    // словари разные. Выбор по головам отдавал второй цели словарь
    // объявляемого инстанса с непривязанным `a`: ядро такой терм отвергает,
    // элаборация принимала. Собрать для неё правильный словарь сегодня нечем -
    // имени у инстанса до конца объявления нет, - и это названный отказ, а не
    // принятая неверная программа.
    let error = refused(&format!(
        "{BASE}{EQ_CLASS}
data List a where
  Nil : List a
  Cons : a -> List a -> List a

instance {{Eqv a}} => Eqv (List a) where
  eq Nil Nil = eq (Cons Zero Nil) (Cons Zero Nil)
  eq p q = False

answer : Bool
answer = eq (Cons Zero Nil) (Cons Zero Nil)
"
    ));
    assert!(
        matches!(error, ElabError::DeclaringInstance { .. }),
        "ожидался отказ про объявляемый инстанс, получено: {error}"
    );
}

#[test]
fn a_class_method_may_have_a_default() {
    // §4.1: умолчание пишется в классе и раскрывается **в инстансе** - тело
    // его зовёт другие методы того же класса, а словарь для них объявляет
    // инстанс. Элаборировать его в классе было бы нечем.
    program(&format!(
        "{BASE}
not : Bool -> Bool
not True = False
not False = True

class Eqv a where
  eq : a -> a -> Bool
  neq : a -> a -> Bool
  neq x y = not (eq x y)

instance Eqv Nat where
  eq a b = True

answer : Bool
answer = neq Zero (Succ Zero)
"
    ));
}

#[test]
fn a_superclass_is_a_field_of_the_dictionary() {
    // §3.5: словарь суперкласса - поле словаря класса, разряжаемое в точке
    // объявления инстанса. Автор его не пишет: поле заполняет поиск.
    program(&format!(
        "{BASE}{EQ_CLASS}
class Ord a when Eqv a where
  cmp : a -> a -> Bool

instance Ord Nat where
  cmp a b = eq a b

used : Bool
used = cmp Zero Zero
"
    ));
}

#[test]
fn a_superclass_is_reached_through_the_context() {
    // Изнутри `{Ord a} =>` словарь `Eqv a` берётся проекцией поля, а не
    // отдельным поиском: инстанса для переменной нет и быть не может.
    program(&format!(
        "{BASE}{EQ_CLASS}
class Ord a when Eqv a where
  cmp : a -> a -> Bool

instance Ord Nat where
  cmp a b = True

both : {{Ord a}} => a -> a -> Bool
both x y = eq x y
"
    ));
}

#[test]
fn an_instance_member_sees_all_its_siblings() {
    // Члены инстанса объявляются **одной группой** (§10 вопрос 50), поэтому
    // словарь для собственной цели собирается из всех сразу: рекурсия в
    // первом же члене работает, и умолчание, зовущее написанный метод, тоже.
    program(&format!(
        "{BASE}
not : Bool -> Bool
not True = False
not False = True

class Eqv a where
  eq : a -> a -> Bool
  neq : a -> a -> Bool
  neq x y = not (eq x y)

instance Eqv Nat where
  eq Zero Zero = True
  eq (Succ a) (Succ b) = eq a b
  eq a b = False

answer : Bool
answer = neq Zero (Succ Zero)
"
    ));
}

#[test]
fn mutual_definitions_see_each_other() {
    // §4.8: члены группы объявляются разом, поэтому ссылка на соседа законна
    // до того, как он попал в сигнатуру. Вердикт тотальности при этом даётся
    // по совместному графу вызовов - без него разворота бы не случилось, и
    // `Wit (even 2)` не принял бы `Yes`.
    program(&format!(
        "{BASE}
data Wit : Bool -> Type where
  Yes : Wit True

mutual
  even : Nat -> Bool
  even Zero = True
  even (Succ k) = odd k

  odd : Nat -> Bool
  odd Zero = False
  odd (Succ k) = even k

computed : Wit (even (Succ (Succ Zero)))
computed = Yes
"
    ));
}

#[test]
fn a_mutual_member_keeps_its_own_level_arity() {
    // §10 вопрос 54, решение 2026-08-31: обобщение идёт по написанному типу
    // каждого члена, а не общее на группу. Ссылка на себя несёт свои
    // параметры, на соседа - свежие дырки; фантомных параметров нет, и `ping`
    // остаётся арности нуль рядом с полиморфным `pong`.
    program(&format!(
        "{BASE}
mutual
  ping : Nat -> Bool
  ping Zero = True
  ping (Succ k) = pong True k

  pong : {{0 a : Type}} -> a -> Nat -> Bool
  pong x Zero = False
  pong x (Succ k) = ping k

used : Bool
used = pong True (Succ Zero)
"
    ));
}

#[test]
fn the_type_of_a_member_may_not_name_a_sibling() {
    // §10 вопрос 64: типы всех членов проверяются до объявления группы, и
    // соседа тип назвать не вправе. Элаборация группы не видела, поэтому
    // строчное имя соседа уходило в свободные и §4.1 поднимала его в
    // implicit-параметр: обёртка в `mutual` не добавляла типу видимости, а
    // отнимала - программа, законная снаружи блока, внутри меняла смысл молча,
    // и отказ всплывал в месте использования как «аргумент не выведен».
    let error = refused(&format!(
        "{BASE}
data P (n : Nat) where
  Mk : P n

mutual
  n : Nat
  n = Zero

  g : P n -> Bool
  g w = True
"
    ));
    assert!(
        matches!(error, ElabError::ModuleMember { .. }),
        "получено {error:?}"
    );
    // Семейство той же группы назвать можно: объявляется оно первым.
    program(&format!(
        "{BASE}
mutual
  data Tree where
    Leaf : Tree

  size : Tree -> Nat
  size Leaf = Zero
"
    ));
}

#[test]
fn an_attribute_inside_a_group_is_not_dropped() {
    // Заголовок члена группы разбирался без атрибутов, и они выбрасывались
    // молча: `@fbip` внутри `mutual` принимался вместо отказа, обещанного
    // §4.7, а `@total` не значил ничего - та же расходящаяся функция
    // отвергалась вне блока и проходила внутри.
    let refuse = |what: &str, text: String| {
        let error = refused(&text);
        assert!(
            matches!(
                error,
                ElabError::Attribute { .. } | ElabError::NotTotal { .. }
            ),
            "{what}: получено {error:?}"
        );
    };
    refuse(
        "@fbip",
        format!("{BASE}\nmutual\n  @fbip\n  a : Nat -> Nat\n  a n = n\n"),
    );
    refuse(
        "@total",
        format!("{BASE}\nmutual\n  @total\n  loopy : Nat -> Nat\n  loopy n = loopy n\n"),
    );
    // И тот же атрибут у метода класса: обещанием за каждый инстанс он быть не
    // вправе - вердикт считается у определения.
    let error = refused(&format!(
        "{BASE}\nclass C a where\n  @total\n  size : a -> a\n"
    ));
    assert!(
        matches!(error, ElabError::ModuleMember { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_diverging_mutual_pair_is_not_total() {
    // Вызов соседа - такая же рекурсия, как свой. Проверка, знавшая только своё
    // имя, не видела в этой паре ни одного вызова и объявляла её тотальной, а
    // §4.7 пускает тотальное в тип: расходимость проходила в стёртый фрагмент.
    // Побуквенно та же расходимость под одним именем отвергалась всегда.
    let error = refused(&format!(
        "{BASE}
data Wit (n : Nat) where
  Mk : Wit n

mutual
  ping : Nat -> Nat
  ping n = pong n

  pong : Nat -> Nat
  pong n = ping n

use : Wit (ping Zero) -> Nat
use w = Zero
"
    ));
    assert!(
        matches!(
            error,
            ElabError::Core {
                ref error,
                ..
            } if matches!(error.kind, ErrorKind::PartialConstant { .. })
        ),
        "получено {error:?}"
    );
}

#[test]
fn mutual_recursion_decreases_at_a_position_of_its_own() {
    // Одной позиции на всю группу не хватает: у `even` убывает нулевой
    // аргумент, у `pong` - второй, потому что перед ним стоит стёртый параметр
    // типа. Позиция ищется каждому члену своя, но согласованно - вызов
    // засчитывается, когда аргумент на позиции вызываемого произошёл разбором
    // от параметра на позиции вызывающего.
    let signature = program(&format!(
        "{BASE}
data Wit (b : Bool) where
  Mk : Wit b

mutual
  even : Nat -> Bool
  even Zero = True
  even (Succ k) = odd True k

  odd : {{0 a : Type}} -> a -> Nat -> Bool
  odd x Zero = False
  odd x (Succ k) = even k

used : Wit (even Zero) -> Bool
used w = True
"
    ));
    assert!(
        signature.lookup("even").is_some_and(|it| it.total),
        "`even` обязана быть тотальной: `Wit (even Zero)` иначе не проверился бы"
    );
}

#[test]
fn a_mutual_group_carries_definitions_and_families() {
    // Названные границы: постулат группой объявлять незачем - он и есть
    // отсутствие тела, - а модуль и класс объявляются отдельно.
    for text in [
        "mutual\n  loose : Nat\n",
        "mutual\n  type Alias = Nat\n",
        "mutual\n  module M where\n    inner : Nat\n    inner = Zero\n",
    ] {
        let error = refused(&format!("{BASE}{text}"));
        assert!(
            matches!(
                error,
                ElabError::MissingSignature { .. } | ElabError::ModuleMember { .. }
            ),
            "для {text:?} получено {error:?}"
        );
    }
}

#[test]
fn the_total_attribute_requires_a_positive_verdict() {
    // §4.7: вердикт ядро считает всегда (лог 2026-08-24), а атрибут - это
    // требование «ответ обязан быть да». Отсюда и отказ: он не о том, что
    // проверка не справилась, а о том, что обещание не выполнено.
    program(&format!(
        "{BASE}
@total
plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)
"
    ));
    let error = refused(&format!(
        "{BASE}
loop : Nat -> Nat
loop n = loop n

@total
bad : Nat -> Nat
bad n = loop n
"
    ));
    assert!(
        matches!(error, ElabError::NotTotal { .. }),
        "получено {error:?}"
    );
}

#[test]
fn an_unchecked_attribute_names_what_is_missing() {
    // `@fbip` и `@noalloc` - обязательства перед backend'ом, а его нет.
    // Принять их молча значило бы обещать проверку, которой не будет.
    for text in ["@fbip\nf : Nat\nf = Zero\n", "@fast\nf : Nat\nf = Zero\n"] {
        let error = refused(&format!("{BASE}{text}"));
        assert!(
            matches!(error, ElabError::Attribute { .. }),
            "для {text:?} получено {error:?}"
        );
    }
}

/// Класс с двумя именованными инстансами на один тип - случай, ради которого
/// имена и существуют (§4.3).
const PICK: &str = "
class Pick a where
  pick : a -> a -> a

instance first : Pick Nat where
  pick a b = a

instance second : Pick Nat where
  pick a b = b
";

#[test]
fn using_chooses_a_named_instance() {
    // §4.3: выбор в месте использования. Выбор действует на **вставку**, а не
    // на отложенный поиск: словарь берётся написанным сразу, потому что у
    // дырки места написания уже не будет.
    program(&format!(
        "{BASE}{PICK}
data Wit : Nat -> Type where
  Yes : Wit Zero

taken : Wit (using first (pick Zero (Succ Zero)))
taken = Yes

pointed : Wit (pick @Nat @first Zero (Succ Zero))
pointed = Yes
"
    ));
}

#[test]
fn several_named_instances_ask_for_a_choice() {
    // Выбрать между ними автоматика не вправе, и молча взять первый - хуже
    // отказа: программа поменяла бы смысл от порядка объявлений.
    let error = refused(&format!(
        "{BASE}{PICK}
bad : Nat
bad = pick Zero Zero
"
    ));
    assert!(
        matches!(error, ElabError::AmbiguousInstance { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_single_named_instance_resolves_by_itself() {
    // Имя - возможность сослаться, а не отказ от автоматики (решение
    // 2026-08-31): пока кандидат один, `using` писать незачем.
    program(&format!(
        "{BASE}
class Pick a where
  pick : a -> a -> a

instance only : Pick Nat where
  pick a b = a

auto : Nat
auto = pick Zero (Succ Zero)
"
    ));
}

/// Класс о **паре** типов: у него ни один параметр не главнее прочих.
const CONV: &str = "
class Conv a b where
  conv : a -> b

instance Conv Nat Bool where
  conv Zero = False
  conv (Succ k) = True

instance Conv Bool Nat where
  conv True = Succ Zero
  conv False = Zero
";

#[test]
fn a_class_takes_several_parameters() {
    // §4.1: кандидат ищется по головам **всех** аргументов, поэтому `Conv Nat
    // Bool` и `Conv Bool Nat` - разные инстансы, а не переобъявление одного.
    program(&format!(
        "{BASE}{CONV}
forward : Bool
forward = conv (Succ Zero)

backward : Nat
backward = conv True
"
    ));
}

#[test]
fn a_candidate_is_keyed_by_every_argument() {
    // Голова первого аргумента подходит, второго - нет. Ключ из одной головы
    // взял бы здесь `Conv Nat Bool` и соврал бы о типе результата.
    let error = refused(&format!(
        "{BASE}
class Conv a b where
  conv : a -> b

instance Conv Nat Bool where
  conv n = True

bad : Nat
bad = conv Zero
"
    ));
    assert!(
        matches!(&error, ElabError::NoInstance { written, .. } if &**written == "Conv Nat Nat"),
        "получено {error:?}"
    );
}

#[test]
fn a_multi_parameter_instance_carries_a_context() {
    // Контекст связывает обе переменные сразу: `b` в голове видно только из
    // второго аргумента.
    program(&format!(
        "{BASE}
data Pair (a : Type) (b : Type) where
  Both : a -> b -> Pair a b

class Conv a b where
  conv : a -> b

instance Conv Nat Bool where
  conv n = True

instance {{Conv a b}} => Conv (Pair a a) (Pair b b) where
  conv (Both x y) = Both (conv x) (conv y)

lifted : Pair Bool Bool
lifted = conv (Both Zero (Succ Zero))
"
    ));
}

#[test]
fn a_head_binds_more_than_one_variable() {
    // Заголовок с двумя связываниями: домен второго - дырка над первым, и
    // подстановка её решения оставляет бета-редекс. Читать заголовок надо из
    // значения, иначе инференс домена спотыкается о лямбду.
    program(&format!(
        "{BASE}
data Pair (a : Type) (b : Type) where
  Both : a -> b -> Pair a b

class Eqv a where
  eq : a -> a -> Bool

instance Eqv Nat where
  eq x y = True

instance Eqv Bool where
  eq x y = False

instance {{Eqv a, Eqv b}} => Eqv (Pair a b) where
  eq (Both x y) (Both p q) = eq x p

mixed : Bool
mixed = eq (Both Zero True) (Both Zero False)
"
    ));
}

#[test]
fn a_multi_parameter_class_keeps_superclasses_and_defaults() {
    // Суперкласс и умолчание метода стоят у класса, а не у ключа поиска, и от
    // числа параметров зависеть не должны.
    program(&format!(
        "{BASE}
class Eqv a where
  eq : a -> a -> Bool

instance Eqv Nat where
  eq x y = True

class Conv a b when Eqv a where
  conv : a -> b
  twice : a -> b
  twice x = conv x

instance Conv Nat Bool where
  conv n = True

defaulted : Bool
defaulted = twice Zero
"
    ));
}

#[test]
fn a_synonym_that_gives_back_its_parameter_has_no_key() {
    // Ключ кандидата - головы аргументов, и они обязаны быть одни у всех
    // написаний одного типа: иначе на тип объявляются два инстанса, и какой
    // возьмётся, решает написание цели. Разворот головы шёл по символам и
    // останавливался на `type Id (a : Type) = a` - под лямбдами там
    // переменная, - поэтому `Key Nat` и `Key (Id Nat)` получали разные ключи и
    // уживались в одном файле при `Id Nat ≡ Nat`, обещая обратное `coherent`.
    let error = refused(&format!(
        "{BASE}
type Id (a : Type) = a

coherent class Key a where
  key : a -> Nat

instance Key Nat where
  key n = Succ n

instance Key (Id Nat) where
  key n = Zero
"
    ));
    assert!(
        matches!(error, ElabError::ProjectingHead { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_coherent_class_takes_one_instance() {
    // §3.5 пункт 3: маркер обещает не более одного инстанса на программу, и
    // имя обещания не снимает - именованных на один тип тоже не бывает.
    program(&format!(
        "{BASE}
coherent class Key a where
  key : a -> Nat

instance Key Nat where
  key n = n

taken : Nat
taken = key (Succ Zero)
"
    ));
    let error = refused(&format!(
        "{BASE}
coherent class Key a where
  key : a -> Nat

instance Key Nat where
  key n = n

instance other : Key Nat where
  key n = Zero
"
    ));
    assert!(
        matches!(&error, ElabError::CoherentDuplicate { written, .. } if &**written == "Key Nat"),
        "получено {error:?}"
    );
}

#[test]
fn a_coherent_context_holds_only_coherent_classes() {
    // §3.5 пункт 1: инстанс с некогерентным контекстом - семейство словарей, а
    // не словарь, и уникальность декларации о значении ничего не говорит.
    let head = format!(
        "{BASE}
data List (a : Type) where
  Nil : List a

class Eqv a where
  eq : a -> a -> Bool

coherent class Key a where
  key : a -> Nat
"
    );
    let error = refused(&format!(
        "{head}
instance {{Eqv a}} => Key (List a) where
  key xs = Zero
"
    ));
    assert!(
        matches!(&error, ElabError::CoherentContext { context, .. } if &**context == "Eqv"),
        "получено {error:?}"
    );
    // Тот же инстанс с когерентным контекстом законен.
    program(&format!(
        "{head}
instance Key Nat where
  key n = n

instance {{Key a}} => Key (List a) where
  key xs = Zero
"
    ));
}

#[test]
fn a_coherent_class_keeps_its_superclasses() {
    // §3.5: суперкласс ограничения не требует. Словарь суперкласса - поле
    // словаря класса, разряжаемое в точке объявления инстанса, и при
    // уникальном инстансе уникально и поле.
    program(&format!(
        "{BASE}
class Eqv a where
  eq : a -> a -> Bool

instance Eqv Nat where
  eq x y = True

coherent class Key a when Eqv a where
  key : a -> Nat

instance Key Nat where
  key n = n
"
    ));
}

#[test]
fn a_synonym_head_names_the_same_instance() {
    // Ключ кандидата берётся после δ: `Alias` и `Nat` - один тип, и двух
    // инстансов на него не бывает. Иначе какой из словарей возьмётся, решало
    // бы написание цели.
    let error = refused(&format!(
        "{BASE}
type Alias = Nat

class Eqv a where
  eq : a -> a -> Bool

instance Eqv Nat where
  eq x y = True

instance Eqv Alias where
  eq x y = False
"
    ));
    assert!(
        matches!(error, ElabError::ModuleMember { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_type_alias_takes_parameters() {
    // §4.1: алиас с параметрами - типовая функция. Пишутся они теми же
    // формами, что у семейства, и означают то же.
    program(&format!(
        "{BASE}
data Pair (a : Type) (b : Type) where
  Both : a -> b -> Pair a b

type Twice a = Pair a a

type Endo (a : Type) = a -> a

pair : Twice Nat
pair = Both Zero (Succ Zero)

same : Endo Bool
same x = x
"
    ));
}

#[test]
fn an_abstract_type_member_takes_parameters() {
    // §4.8: абстрактный типовой член с параметрами - объявление типовой
    // функции. Аннотация `:` представление оставляет видимой, поэтому
    // `Clear.Bag Bool` разворачивается до написанного.
    program(&format!(
        "{BASE}
module type BagSig where
  type Bag (a : Type)
  empty : {{a : Type}} -> Bag a

module Clear : BagSig where
  type Bag (a : Type) = a -> Bool
  empty : {{a : Type}} -> Bag a
  empty x = False

seen : Bool -> Bool
seen x = Clear.empty x
"
    ));
}

#[test]
fn a_sealed_parametrised_member_hides_its_representation() {
    // `:>` запечатывает: снаружи `Bag a` - абстрактный тип, а не своё
    // представление, и число параметров этому ничего не меняет.
    let error = refused(&format!(
        "{BASE}
module type BagSig where
  type Bag (a : Type)
  empty : {{a : Type}} -> Bag a

module Sealed :> BagSig where
  type Bag (a : Type) = a -> Bool
  empty : {{a : Type}} -> Bag a
  empty x = False

hidden : Bool -> Bool
hidden x = Sealed.empty x
"
    ));
    assert!(error.to_string().contains("Bag"), "получено {error:?}");
}

#[test]
fn a_dotted_name_is_the_lifted_member() {
    // Снаружи `M.f` есть ссылка на поднятый член, а не проекция из записи
    // (решение 2026-08-31). Проекция теряла параметры уровня тех членов,
    // которых не касалась: поле записи полиморфным по уровню не бывает, и
    // модуль обобщался целиком.
    program(&format!(
        "{BASE}
module Plain where
  ident : {{a : Type}} -> a -> a
  ident x = x
  other : Bool
  other = True

taken : Bool
taken = Plain.other

applied : Nat
applied = Plain.ident Zero
"
    ));
}

#[test]
fn a_nested_member_is_named_by_its_path() {
    // Правило одно на любую глубину: каждое звено точечного имени - имя.
    program(&format!(
        "{BASE}
module Outer where
  module Inner where
    flag : Bool
    flag = True
  near : Bool
  near = Inner.flag

deep : Bool
deep = Outer.Inner.flag
"
    ));
}

#[test]
fn sealing_reaches_the_lifted_members() {
    // Запечатывание держалось на том, что `M.f` - проекция из непрозрачной
    // записи. Раз `M.f` стало именем, флаг переехал на сами имена: иначе `:>`
    // протекал бы через них.
    let head = format!(
        "{BASE}
module type FlagSig where
  type Flag
  make : Flag
  read : Flag -> Bool

module Sealed :> FlagSig where
  type Flag = Bool
  make : Flag
  make = True
  read : Flag -> Bool
  read f = f
"
    );
    // Своими членами запечатанный модуль пользуется как обычно.
    program(&format!(
        "{head}
used : Bool
used = Sealed.read Sealed.make
"
    ));
    // А представление снаружи не видно.
    let error = refused(&format!(
        "{head}
leaked : Bool
leaked = Sealed.read True
"
    ));
    assert!(
        error.to_string().contains("Sealed.Flag"),
        "получено {error:?}"
    );
}

#[test]
fn a_functor_member_takes_its_parameter_written() {
    // Член функтора поднят вместе с параметром, и параметр стоит у него
    // implicit-связыванием. Раз имя доступно снаружи, `@` его и пишет -
    // вывести его там нечем.
    program(&format!(
        "{BASE}
module type Elem where
  type T

module Twin (E : Elem) where
  pick : E.T -> E.T
  pick x = x

module BoolElem where
  type T = Bool

used : Bool -> Bool
used x = Twin.pick @BoolElem x
"
    ));
}

/// Сигнатура, запечатывающая `Bag`, и операция с констрейнтом на его
/// параметре - форма, которую §3.5 и запрещает.
const BAGSIG: &str = "
class Eqv a where
  eq : a -> a -> Bool

module type BagSig where
  type Bag (a : Type)
  empty : {a : Type} -> Bag a
  add : {a : Type} -> {Eqv a} => a -> Bag a -> Bag a
";

/// Тело модуля к ней.
const BAGBODY: &str = "
  type Bag (a : Type) = a -> Bool
  empty : {a : Type} -> Bag a
  empty x = False
  add : {a : Type} -> {Eqv a} => a -> Bag a -> Bag a
  add x b = b
";

#[test]
fn sealing_refuses_a_constraint_on_its_own_parameter() {
    // §3.5: инстанс, участвовавший в построении значения абстрактного типа,
    // переживает вызов, а тип о нём молчит. `Bag a`, собранный под одним
    // `Eqv a` и опрошенный под другим, типизируется обеими сторонами.
    let error = refused(&format!(
        "{BASE}{BAGSIG}
module Sealed :> BagSig where{BAGBODY}"
    ));
    assert!(
        matches!(&error, ElabError::SealedConstraint { class, param, sealed, .. }
            if &**class == "Eqv" && &**param == "a" && &**sealed == "Bag"),
        "получено {error:?}"
    );
    // Область действия - только запечатывающий модуль: при `:` представление
    // видно, и осаждать нечего.
    program(&format!(
        "{BASE}{BAGSIG}
module Clear : BagSig where{BAGBODY}"
    ));
}

#[test]
fn a_coherent_class_passes_the_sealing_rule() {
    // Маркер и заведён затем, чтобы такая сигнатура запечатывала: при одном
    // инстансе на программу осадок один и тот же.
    program(&format!(
        "{BASE}
coherent class Key a where
  key : a -> Bool

module type BagSig where
  type Bag (a : Type)
  add : {{a : Type}} -> {{Key a}} => a -> Bag a -> Bag a

module Sealed :> BagSig where
  type Bag (a : Type) = a -> Bool
  add : {{a : Type}} -> {{Key a}} => a -> Bag a -> Bag a
  add x b = b
"
    ));
}

#[test]
fn a_constraint_beside_the_sealed_type_is_legal() {
    // Правило про параметр запечатанного типа, а не про констрейнты вообще:
    // `b` аргументом `Bag` не стоит, и осаждать его не в чем.
    program(&format!(
        "{BASE}
class Eqv a where
  eq : a -> a -> Bool

module type BagSig where
  type Bag (a : Type)
  size : {{a : Type}} -> Bag a -> Bool
  cmp : {{b : Type}} -> {{Eqv b}} => b -> b -> Bool

module Sealed :> BagSig where
  type Bag (a : Type) = a -> Bool
  size : {{a : Type}} -> Bag a -> Bool
  size b = True
  cmp : {{b : Type}} -> {{Eqv b}} => b -> b -> Bool
  cmp x y = eq x y
"
    ));
}

#[test]
fn an_instance_context_cannot_settle_a_sealed_parameter() {
    // Контексты инстансов включены в правило намеренно: иначе та же форма
    // пишется в обход сигнатур.
    let head = format!(
        "{BASE}
class Eqv a where
  eq : a -> a -> Bool

class Show a where
  render : a -> Bool

module type BagSig where
  type Bag (a : Type)
  empty : {{a : Type}} -> Bag a
"
    );
    let body = "
  type Bag (a : Type) = a -> Bool
  empty : {a : Type} -> Bag a
  empty x = False
";
    let error = refused(&format!(
        "{head}
module Sealed :> BagSig where{body}
instance {{Eqv a}} => Show (Sealed.Bag a) where
  render b = True
"
    ));
    assert!(
        matches!(&error, ElabError::SealedInstance { class, sealed, .. }
            if &**class == "Eqv" && &**sealed == "Sealed.Bag"),
        "получено {error:?}"
    );
    // Незапечатанный тип правилу не подлежит.
    program(&format!(
        "{head}
module Clear : BagSig where{body}
instance {{Eqv a}} => Show (Clear.Bag a) where
  render b = True
"
    ));
}

#[test]
fn mutual_families_are_declared_together() {
    // `Tree` и `Forest` друг без друга не объявляются - случай, ради которого
    // `mutual` и написан. Единица объявления у семейств общая, и фаза
    // конструкторов у ядра идёт раньше тел.
    program(&format!(
        "{BASE}
mutual
  data Tree (a : Type) where
    Node : a -> Forest a -> Tree a

  data Forest (a : Type) where
    Nil : Forest a
    Cons : Tree a -> Forest a -> Forest a

one : Tree Bool
one = Node True Nil
"
    ));
}

#[test]
fn a_mutual_group_mixes_families_and_definitions() {
    // Семейства объявляются первыми и своей группой: разбор берёт у
    // конструктора тип, и в сигнатуре он обязан быть раньше клауз.
    program(&format!(
        "{BASE}
mutual
  data Tree where
    Node : Forest -> Tree

  data Forest where
    Nil : Forest
    Cons : Tree -> Forest -> Forest

  size : Tree -> Nat
  size (Node f) = sizes f

  sizes : Forest -> Nat
  sizes Nil = Zero
  sizes (Cons t f) = size t
"
    ));
}

#[test]
fn positivity_is_measured_over_the_whole_group() {
    // `A` становится негативным через `B` ровно так же, как через себя:
    // `A ≅ B -> Bool` и `B ≅ A` дают `A ≅ A -> Bool`, то есть жителя любого
    // типа. Проверка, знающая только своё имя, такую пару принимала бы.
    let error = refused(&format!(
        "{BASE}
mutual
  data A where
    MkA : (B -> Bool) -> A

  data B where
    MkB : A -> B
"
    ));
    // Названо **найденное** семейство, а не проверяемое: написано в поле `B`,
    // и искать надо там.
    let message = error.to_string();
    assert!(
        message.contains("`MkA` использует `B` в отрицательной позиции"),
        "получено {message}"
    );
}

#[test]
fn a_trailing_parameter_takes_a_default() {
    // §4.1: умолчание срабатывает по **написанной** арности применения, до
    // всякого вывода. `Pair Nat` есть `Pair Nat Nat`, а написанные оба
    // параметра умолчание не трогает.
    program(&format!(
        "{BASE}
data Pair (a : Type) (b = a) where
  Both : a -> b -> Pair a b

homo : Pair Nat
homo = Both Zero (Succ Zero)

hetero : Pair Nat Bool
hetero = Both Zero True

type Store (a : Type) (idx = Nat) = idx -> a

kept : Store Bool
kept n = True
"
    ));
}

#[test]
fn a_class_parameter_takes_a_default() {
    // Мотивирующий случай §4.3: `Mul` гетерогенен, а однородное применение
    // возвращается умолчанием - `Mul Int` есть `Mul Int Int`.
    program(&format!(
        "{BASE}
class Mul a (b = a) where
  mul : a -> b -> a

instance Mul Nat where
  mul x y = x

instance Mul Nat Bool where
  mul x y = x

homo : Nat
homo = mul Zero Zero

hetero : Nat
hetero = mul Zero True
"
    ));
}

#[test]
fn a_default_belongs_to_a_trailing_parameter() {
    // §4.1, правило 2: иначе понадобился бы позиционный пропуск (`Mul _ Int`),
    // то есть вторая нотация ради редкого случая.
    let error = refused(&format!(
        "{BASE}
data Pair (a = Nat) (b : Type) where
  Both : a -> b -> Pair a b
"
    ));
    assert!(
        matches!(&error, ElabError::TrailingDefault { name, .. } if &**name == "b"),
        "получено {error:?}"
    );
}

#[test]
fn a_case_over_a_resource_is_written() {
    // §10 вопрос 82, расхождение (3): разбор по ресурсу отвергался, тогда как
    // побуквенно та же функция клаузами работала. Причина была в форме -
    // подъём применял разбор ко всему контексту, а применение расходует.
    program(
        "\
data Bool where
  True : Bool
  False : Bool

resource Socket where
  Listen : Socket
  close : (1 s : Socket) -> Bool
  close s = True

byCase : (1 s : Socket) -> Bool
byCase s = case s of
  Listen -> True
",
    );
}

#[test]
fn recursion_through_a_case_is_structural() {
    // Расхождение (4): размеры терялись под поднятым `case`, и рекурсия через
    // него структурной не считалась никогда. Разбор выражением даёт теперь тот
    // же терм, что и клаузы, поэтому вердикт у них один.
    program(&format!(
        "{BASE}
@total
count : Nat -> Nat
count n = case n of
  Zero -> Zero
  Succ k -> count k
"
    ));
}

#[test]
fn a_branch_does_not_wash_out_scope_binding() {
    // Расхождение (1): позиция не доходила до ветвей, и `if c then k else k`
    // выносил наружу то, что прямое `k` вынести не может. Разбор значения не
    // строит - их строят ветви, и позиция достаётся каждой.
    let error = refused(
        "\
data Bool where
  True : Bool
  False : Bool

forwardIf : (1 k : Bool -> Bool) -> Bool -> Bool -> Bool
forwardIf k c = if c then k else k
",
    );
    assert!(
        matches!(&error, ElabError::ScopeBound { name, .. } if &**name == "k"),
        "получено {error:?}"
    );
}

#[test]
fn a_case_leaves_untouched_bindings_alone() {
    // Расхождение (2): применение к контексту засчитывалось как употребление
    // каждого связывания, включая те, которых ни одна ветвь не называет.
    // Ресурс, о котором тело забыло, получал `drop` плюс применение и
    // становился ω.
    program(
        "\
data Bool where
  True : Bool
  False : Bool

resource File where
  Open : File
  close : (1 h : File) -> Bool
  close h = True

forgotten : (1 h : File) -> Bool -> Bool
forgotten h c = case c of
  True -> True
  False -> False
",
    );
}

/// Ресурс с деструктором и разбор по нему в двух ветвях.
const FORGETFUL: &str = "
data Bool where
  True : Bool
  False : Bool

resource File where
  Open : File
  close : (1 h : File) -> Bool
  close h = True

pick : (1 h : File) -> Bool -> Bool
pick h c = case c of
  True -> close h
  False -> True
";

#[test]
fn a_branch_closes_what_it_forgot() {
    // §10 вопрос 71 переоткрыт разбором выражением: «клауза и есть ветвь»
    // верно ровно до тех пор, пока ветвь не заведена **внутри** того, что
    // видит правило вставки. Одна ветвь расходует `h`, другая забыла - и
    // забывшая обязана закрыть его сама, иначе второй путь течёт.
    let signature = program(FORGETFUL);
    let body = signature
        .lookup("pick")
        .and_then(|definition| definition.body.clone())
        .expect("`pick` объявлено");
    let rendered = body.to_string();
    assert_eq!(
        rendered.matches("close").count(),
        2,
        "закрыт только один путь: {rendered}"
    );
}

#[test]
fn every_branch_closes_every_resource_it_forgot() {
    // Правило поветвенное и по каждому ресурсу отдельно: ветвь, закрывшая
    // один, обязана закрыть и второй - путь у неё один на оба.
    let signature = program(
        "\
data Bool where
  True : Bool
  False : Bool

resource File where
  Open : File
  close : (1 h : File) -> Bool
  close h = True

both : (1 a : File) -> (1 b : File) -> Bool -> Bool
both a b c = case c of
  True -> close a
  False -> close b
",
    );
    let body = signature
        .lookup("both")
        .and_then(|definition| definition.body.clone())
        .expect("`both` объявлено");
    let rendered = body.to_string();
    assert_eq!(
        rendered.matches("close").count(),
        4,
        "в каждой ветви должно быть по два закрытия: {rendered}"
    );
}

#[test]
fn a_nested_branch_closes_what_it_forgot() {
    // Вложенный разбор - тот же разбор: правило применяется на каждом, а не
    // один раз на самый внешний.
    let signature = program(
        "\
data Bool where
  True : Bool
  False : Bool

resource File where
  Open : File
  close : (1 h : File) -> Bool
  close h = True

nested : (1 h : File) -> Bool -> Bool -> Bool
nested h c d = case c of
  True -> case d of
    True -> close h
    False -> True
  False -> True
",
    );
    let body = signature
        .lookup("nested")
        .and_then(|definition| definition.body.clone())
        .expect("`nested` объявлено");
    let rendered = body.to_string();
    assert_eq!(
        rendered.matches("close").count(),
        3,
        "закрыт не всякий путь: {rendered}"
    );
}

#[test]
fn a_branch_closes_what_its_own_pattern_bound() {
    // Поле, связанное паттерном ветви, - такое же владение, как аргумент, и
    // клауза закрывает его тем же правилом. В ветви `case` этого не делалось
    // вовсе: вставка собиралась только из ресурсов объемлющего scope, а
    // `closing_of` по собственным переменным не звался. Побуквенно одинаковые
    // `byClause` и `byCase` расходились - первая закрывала, вторая уносила.
    let signature = program(
        "\
data Bool where
  True : Bool
  False : Bool

resource File where
  Open : File
  close : (1 h : File) -> Bool
  close h = True

resource Socket where
  Listen : File -> Socket
  shut : (1 s : Socket) -> Bool
  shut (Listen h) = close h

byClause : Socket -> Bool
byClause (Listen h) = True

byCase : Socket -> Bool
byCase s = case s of
  Listen h -> True
",
    );
    for name in ["byClause", "byCase"] {
        let body = signature
            .lookup(name)
            .and_then(|definition| definition.body.clone())
            .unwrap_or_else(|| panic!("`{name}` объявлено"));
        let rendered = body.to_string();
        assert_eq!(
            rendered.matches("close").count(),
            1,
            "у `{name}` поле паттерна не закрыто: {rendered}"
        );
    }
}

#[test]
fn a_shadowing_pattern_does_not_capture_the_insertion() {
    // Индекс закрываемого извне считается до спуска в ветвь: внутри неё имя
    // затеняется переменной паттерна, а поиск идёт изнутри наружу. Вставка
    // промахивалась мимо того, что обязана была закрыть, - корректная
    // программа отвергалась несовпадением типов, а путь с затенением уносил
    // внешний дескриптор молча.
    let signature = program(
        "\
data Bool where
  True : Bool
  False : Bool

resource File where
  Open : File
  close : (1 h : File) -> Bool
  close h = True

data Box where
  Empty : Box
  Full : Bool -> Box

shadow : (1 h : File) -> Box -> Bool
shadow h b = case b of
  Empty -> close h
  Full h -> h
",
    );
    let body = signature
        .lookup("shadow")
        .and_then(|definition| definition.body.clone())
        .expect("`shadow` объявлено");
    let rendered = body.to_string();
    assert_eq!(
        rendered.matches("close").count(),
        2,
        "затенённый путь не закрыт: {rendered}"
    );
}

#[test]
fn a_resource_no_branch_names_is_closed_once() {
    // Граница правила с двух сторон. Ресурс, которого не называет ни одна
    // ветвь, закрывает правило снаружи - вставить его ещё и в каждую ветвь
    // значило бы закрыть дважды. Ресурс, который называют все, закрывать не
    // надо вовсе.
    let signature = program(
        "\
data Bool where
  True : Bool
  False : Bool

resource File where
  Open : File
  close : (1 h : File) -> Bool
  close h = True

forgotten : (1 h : File) -> Bool -> Bool
forgotten h c = case c of
  True -> True
  False -> False

everywhere : (1 h : File) -> Bool -> Bool
everywhere h c = case c of
  True -> close h
  False -> close h
",
    );
    for (name, expected) in [("forgotten", 1), ("everywhere", 2)] {
        let body = signature
            .lookup(name)
            .and_then(|definition| definition.body.clone())
            .unwrap_or_else(|| panic!("`{name}` объявлено"));
        let rendered = body.to_string();
        assert_eq!(
            rendered.matches("close").count(),
            expected,
            "у `{name}` закрытий не столько: {rendered}"
        );
    }
}

#[test]
fn the_effect_sort_is_written_and_inhabited() {
    // §3.4: `effect State s where …` объявляет `State : Type ℓ -> Effect`, то
    // есть формер метки оканчивается сортом `Effect`. Сорт устроен по образцу
    // `Level`: населяют его метки, а не типы, и уровня у него нет - метка
    // ничего не содержит.
    program(&format!(
        "{BASE}
State : Type -> Effect

Reader : Effect

named : Effect
named = Reader

applied : Effect
applied = State Nat
"
    ));
    // Тип и эффект - разные сорта, и населять один другим нечем.
    let error = refused(&format!(
        "{BASE}
wrong : Effect
wrong = Zero
"
    ));
    assert!(error.to_string().contains("Effect"), "получено {error:?}");
}

#[test]
fn a_row_is_written_on_the_arrow() {
    // §3.4: row описывает, что происходит при применении, и стоит полем
    // стрелки. Написанная перед типом результата, она снимается туда же.
    let signature = program(&format!(
        "{BASE}
State : Type -> Effect

step : Bool -> {{State Bool}} Bool
"
    ));
    let ty = signature
        .lookup("step")
        .map(|definition| definition.ty.to_string())
        .expect("`step` объявлено");
    assert!(ty.contains("State Bool"), "row не попала в тип: {ty}");
}

#[test]
fn a_label_must_end_in_the_effect_sort() {
    // Метка - конструктор эффекта, а не любое имя: `{Maybe Int}` не row, и
    // сказать об этом должен тот, кто её читает. Проверяет это обычный вывод
    // типа применения - второго правила для того же вопроса не нужно.
    let error = refused(&format!(
        "{BASE}
Wrong : Type -> Type

step : Bool -> {{Wrong Bool}} Bool
"
    ));
    assert!(
        matches!(&error, ElabError::NotAnEffect { name, .. } if &**name == "Wrong"),
        "получено {error:?}"
    );
}

#[test]
fn a_suspended_computation_is_a_function_of_unit() {
    // §3.4: `{ε} A` есть нульместная функция `(ω _ : Unit) -> ε ▷ A`, а
    // нульместных функций в ядре нет - их место занимает аргумент-единица.
    // Берётся она по имени, тем же соглашением, каким `if` берёт `Bool`.
    program(&format!(
        "{BASE}
data Unit where
  MkUnit : Unit

State : Type -> Effect

counter : {{State Bool}} Bool
counter u = True

taken : ({{State Bool}} Bool) -> {{State Bool}} Bool
taken c = c MkUnit
"
    ));
    // Не объявлена - отказывает обычный поиск имени, и говорит он про имя.
    let error = refused(&format!(
        "{BASE}
State : Type -> Effect

counter : {{State Bool}} Bool
counter u = True
"
    ));
    assert!(
        matches!(&error, ElabError::UnknownName { name, .. } if &**name == "Unit"),
        "получено {error:?}"
    );
}

#[test]
fn a_written_row_tail_names_one_parameter_per_name() {
    // Написанный хвост закрывает подъём на своей позиции: полиморфизмом там
    // управляет программист (§3.4). Одно имя - один параметр, сколько бы раз
    // оно ни встретилось; позиция без написанной row берёт переменную подъёма,
    // и она у сигнатуры одна.
    let signature = program(&format!(
        "{BASE}
State : Type -> Effect

Log : Effect

named : Bool -> {{State Bool | e}} Bool
shared : Bool -> {{Log | e}} (Bool -> {{State Bool | e}} Bool)
apart : Bool -> Bool -> {{State Bool | e}} Bool
"
    ));
    let arity = |name: &str| signature.lookup(name).expect("объявлено").row_arity;
    assert_eq!(arity("named"), 1, "написанный хвост - один параметр");
    assert_eq!(arity("shared"), 1, "два вхождения имени - тот же параметр");
    assert_eq!(
        arity("apart"),
        2,
        "позиция без записи берёт переменную подъёма"
    );
}

#[test]
fn an_operation_may_not_be_called_return() {
    // `return` - имя ветки **значения** вычисления (§3.4, §4.1), и операция с
    // тем же именем делает из одной написанной ветки две: у элиминатора это
    // разные связывания. Проверялось это нигде, а расходились слоты молча -
    // при операции-вычислении они получают структурно один тип, хендлер
    // проходит проверку, и одна ветка исполняет две роли.
    let error = refused(
        "\
data Bool where
  True : Bool

data Unit where
  MkUnit : Unit

effect Log where
  return : {Log} Bool
",
    );
    assert!(
        matches!(error, ElabError::ReservedOperation { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_clause_with_a_carried_neighbour_keeps_its_ambient_row() {
    // Стрелки, в которые компилятор клауз заворачивает вынесенных соседей,
    // несут окружающую row: ветвь есть часть разбора, разбор работает в
    // окружающей (§3.4). Снималась она с телескопа вместе с отбрасыванием
    // самой row, поэтому контекст разбора был пуст, стрелки объявляли «чисто»,
    // и клауза с эффектным телом отвергалась непогашенностью в теле функции,
    // чья сигнатура эту row и написала.
    let text = "\
data Bool where
  True : Bool
  False : Bool

data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Vect : Nat -> Type where
  Nil : Vect Zero
  Cons : (0 n : Nat) -> Bool -> Vect n -> Vect (Succ n)

effect State s where
  put : s -> Unit

step : Bool -> {State Bool} Unit
step b = put b
";
    // Вторая колонка зависит от уточняемого уровня - её компилятор и выносит.
    program(&format!(
        "{text}
both : (0 n : Nat) -> Vect n -> Vect n -> {{State Bool}} Unit
both n Nil ys = MkUnit
both n (Cons k x xs) ys = step x
"
    ));
    // Направление проверки: чистая сигнатура при том же теле обязана
    // отвергаться, иначе тест ловил бы не то.
    let error = refused(&format!(
        "{text}
both : (0 n : Nat) -> Vect n -> Vect n -> Unit
both n Nil ys = MkUnit
both n (Cons k x xs) ys = step x
"
    ));
    assert!(
        error.to_string().contains("не погашены"),
        "получено {error:?}"
    );
}

#[test]
fn a_row_hole_does_not_outlive_its_declaration() {
    // Дырка, дожившая до сигнатуры, зависит от хранилища, которого за границей
    // группы уже нет. Для уровня и терма это отказ с Фазы 2, для row сорт
    // добавлен Фазой 4, а отказа к нему не завели - и дырка уезжала в
    // сохранённый тип **живой**, роняя компилятор позже, в чужой группе, где
    // зонканье бралось за неё после `release`.
    //
    // Написанный хвост в типе члена класса связать сегодня нечем: типы членов
    // не идут через `declared_type`, поэтому ни свободные имена, ни хвосты там
    // не поднимаются. Тест закрепляет **ворота**, а не желаемое поведение:
    // отказ по месту вместо падения в другом объявлении.
    let error = refused(
        "\
data Bool where
  True : Bool

data Unit where
  MkUnit : Unit

effect State s where
  put : s -> Unit

class Runner a where
  run : a -> {State Bool | e} Bool
",
    );
    assert!(
        matches!(
            error,
            ElabError::Core { ref error, .. }
                if matches!(error.kind, ErrorKind::UnsolvedDefinitionRow { .. })
        ),
        "получено {error:?}"
    );
    // Там, где хвост связывается, он по-прежнему работает.
    program(
        "\
data Bool where
  True : Bool

data Unit where
  MkUnit : Unit

effect State s where
  put : s -> Unit

top : Bool -> {State Bool | e} Unit
top b = put b
",
    );
}

#[test]
fn an_effect_declares_a_label_and_its_operations() {
    // §3.4: `effect` устроен как data-объявление - формер плюс члены, чьи типы
    // обязаны упоминать формер в предписанной позиции. Позиция эта row, а не
    // результат: операция не строит значение метки, она её производит.
    let signature = program(&format!(
        "{BASE}
data Unit where
  MkUnit : Unit

effect State s where
  get : s
  put : s -> Unit
"
    ));
    assert_eq!(
        signature
            .lookup("State")
            .expect("метка объявлена")
            .effect_shape(),
        Some(1),
        "у метки один параметр"
    );
    // Операция - постулат: развернуть её нечем, пока хендлер не подставит
    // evidence, и потому расходиться нечему.
    let put = signature.lookup("put").expect("операция объявлена");
    assert!(
        put.body.is_none() && put.total,
        "операция - тотальный постулат"
    );
}

#[test]
fn an_operation_produces_exactly_its_own_label() {
    // Row операции либо пишут, либо нет, и обе записи законны: §3.4 пишет
    // `yield : a -> ()`, §3.6 пишет `allocIn : … -> {Alloc r} (Ref r a)`.
    // Проверяется же одно и то же - что производится ровно объявляемая метка,
    // применённая к собственным параметрам.
    let head = format!(
        "{BASE}
data Unit where
  MkUnit : Unit

Log : Effect
"
    );
    program(&format!(
        "{head}
effect State s where
  put : s -> {{State s}} Unit
"
    ));
    for written in [
        "put : s -> {Log} Unit",
        "put : s -> {State s, Log} Unit",
        "put : s -> {Log | e} Unit",
    ] {
        let error = refused(&format!(
            "{head}
effect State s where
  {written}
"
        ));
        assert!(
            error.to_string().contains("обязана производить ровно"),
            "для {written:?} получено {error:?}"
        );
    }
    // Параметры повторяются дословно - тем же правилом, каким конструктор
    // повторяет параметры своего семейства.
    let error = refused(&format!(
        "{head}
effect Both a b where
  op : a -> {{Both a a}} Unit
"
    ));
    assert!(
        error.to_string().contains("обязана производить ровно"),
        "получено {error:?}"
    );
}

#[test]
fn a_computation_is_run_or_passed_by_the_expected_type() {
    // §3.4: одна и та же запись означает «передать вычисление» и «выполнить
    // его», а различает их ожидаемый тип. Проверяются все три позиции, где
    // написанный тип элаборации известен: тело клаузы, аргумент применения,
    // аннотация `let`.
    let head = format!(
        "{BASE}
data Unit where
  MkUnit : Unit

effect State s where
  get : s
"
    );
    program(&format!(
        "{head}
-- Ожидается `Bool` - исполняется.
peek : Bool -> {{State Bool}} Bool
peek b = get

-- Ожидается вычисление - передаётся как есть.
runState : Bool -> ({{State Bool}} Bool) -> Bool

passed : Bool -> Bool
passed b = runState b get

-- Аннотация решает то же самое.
bound : Bool -> {{State Bool}} Bool
bound b =
  let n : Bool = get
  n
"
    ));
    // Исполнение обязано гаситься окружающей - отдельного послабления у него
    // нет. Без правила отказ был бы про несовпадение типов, а он про эффекты.
    let error = refused(&format!(
        "{head}
peek : Bool -> Bool
peek b = get
"
    ));
    assert!(
        error.to_string().contains("не погашены"),
        "получено {error:?}"
    );
}

#[test]
fn a_statement_runs_for_its_effects_and_drops_its_value() {
    // §3.4: последовательность собственного узла не имеет - эффекты копятся в
    // суждении, - поэтому оператор есть связывание, которого никто не
    // упоминает. Кратность `1`: значение, потребившее что-то линейное, при `ω`
    // оказалось бы израсходовано сверх меры.
    program(&format!(
        "{BASE}
data Unit where
  MkUnit : Unit

effect State s where
  get : s
  put : s -> Unit

swap : Bool -> {{State Bool}} Bool
swap b =
  put b
  put True
  get
"
    ));
    // Значение оператора владеемого типа отбрасывается молча - вставка `drop`
    // решается по написанному типу, а у оператора его нет (§3.3).
    let error = refused(&format!(
        "{BASE}
resource File where
  Open : Bool -> File
  close : File -> Bool
  close (Open b) = b

use : Bool -> Bool
use b =
  Open b
  b
"
    ));
    assert!(
        error.to_string().contains("отбрасывается"),
        "получено {error:?}"
    );
    // Голова читается после подстановки решений и δ. Без этого ворота
    // обходились всяким выражением, чей результирующий тип **выведен**, а не
    // написан: у разбора выражением мотив - свежая дырка, у полиморфного
    // вызова кодомен приходит нейтралью с дыркой в голове. Ресурс уезжал
    // молча, тогда как монотипный тот же ресурс отвергался.
    for what in [
        "  case b of\n    True -> Open True\n    False -> Open False",
        "  idf (Open b)",
    ] {
        let error = refused(&format!(
            "{BASE}
resource File where
  Open : Bool -> File
  close : File -> Bool
  close (Open b) = b

idf : {{a : Type}} -> a -> a
idf x = x

use : Bool -> Bool
use b =
{what}
  b
"
        ));
        assert!(
            error.to_string().contains("отбрасывается"),
            "{what}: получено {error:?}"
        );
    }
}

#[test]
fn any_function_from_unit_is_a_computation() {
    // Названная цена сахара: `{ε} A` есть `(ω _ : Unit) -> ε ▷ A`, то есть
    // собственного типа у вычисления нет. Значит и всякая написанная руками
    // функция от единицы исполняется по тому же правилу - различить их нечем,
    // и заводить различие значило бы заводить второй тип.
    program(&format!(
        "{BASE}
data Unit where
  MkUnit : Unit

mk : Unit -> Bool
mk u = True

got : Bool
got = mk
"
    ));
}

#[test]
fn an_operation_without_arrows_is_a_computation() {
    // `get : s` есть `{State s} s`, то есть приостановленное вычисление
    // (§3.4). Отдельного случая для него нет: та же дописанная row, просто
    // дописывать её некуда, кроме как в сам тип.
    program(&format!(
        "{BASE}
data Unit where
  MkUnit : Unit

effect State s where
  get : s

peek : {{State Bool}} Bool
peek = get
"
    ));
    // Операция со стрелками под чужой окружающей не гасится - обычное правило
    // погашения, и никакого отдельного статуса у операции в нём нет.
    let error = refused(&format!(
        "{BASE}
data Unit where
  MkUnit : Unit

effect State s where
  put : s -> Unit

silent : Bool -> Unit
silent b = put b
"
    ));
    assert!(
        error.to_string().contains("не погашены"),
        "получено {error:?}"
    );
}

#[test]
fn a_signature_without_a_written_row_is_row_polymorphic() {
    // Auto-lift (§3.4): позиция без написанной `{}` получает ту же свежую
    // переменную, что и прочие позиции сигнатуры, и при вызове она
    // инстанцируется окружающей. Проверяются три следствия сразу: написанное
    // без эффектов зовётся под эффектной окружающей; разбор её не сбрасывает -
    // ветвь работает в той же row, что и сам разбор; общая переменная связывает
    // row колбэка с row результата, и потому higher-order композируется.
    program(&format!(
        "{BASE}
State : Type -> Effect

flip : Bool -> Bool
flip True = False
flip False = True

under : Bool -> {{State Bool}} Bool
under b = flip b

carried : (Bool -> {{State Bool}} Bool) -> Bool -> {{State Bool}} Bool
carried f b = f (flip b)
"
    ));
}

#[test]
fn a_pure_call_needs_no_evidence_and_so_needs_no_row() {
    // Пустая row вызываемого гасится любой окружающей (§3.4): Λ без хвоста
    // требуется потому, что её длина есть смещение вектора evidence, а тому,
    // кто не производит ничего, вектор не передаётся вовсе. Замкнута row у
    // всякого конструктора - `data` пишется без эффектов, - и без этого случая
    // `Succ` под открытой окружающей был бы незовущимся.
    program(&format!(
        "{BASE}
State : Type -> Effect

counted : Nat -> {{State Bool}} Nat
counted n = Succ n

lifted : Nat -> Nat
lifted n = Succ n
"
    ));
}

#[test]
fn an_effect_must_be_discharged_by_the_surrounding_row() {
    // §3.4: применение допустимо, когда окружающая row есть row вызываемого,
    // расширенная слева замкнутым набором меток. Отсюда две стороны: чистая
    // функция эффектную не зовёт, а под своей row - зовёт.
    let head = format!(
        "{BASE}
State : Type -> Effect

Log : Effect

step : Bool -> {{State Bool}} Bool
step b = b
"
    );
    program(&format!(
        "{head}
same : Bool -> {{State Bool}} Bool
same b = step b

wider : Bool -> {{Log, State Bool}} Bool
wider b = step b
"
    ));
    // Пустая окружающая не гасит ничего - в том числе и в стёртом фрагменте,
    // где она пуста всегда.
    let error = refused(&format!(
        "{head}
pure : Bool -> Bool
pure b = step b
"
    ));
    assert!(
        error.to_string().contains("не погашены"),
        "получено {error:?}"
    );
}

fn effects() -> String {
    format!(
        "{BASE}
data Unit where
  MkUnit : Unit

effect Log where
  note : Bool -> Unit

effect State s where
  get : s
  put : s -> Unit

program : {{State Bool}} Bool
program = get
"
    )
}

#[test]
fn a_handler_removes_the_first_occurrence_of_its_label() {
    // §3.4: `handle e with …` снимает первое вхождение метки, а результат
    // работает в остатке. Метка не пишется - её называют ветки.
    program(&format!(
        "{}
run : Bool
run = handle program with
  return v -> v
  get -> resume True
  put x -> resume MkUnit
",
        effects()
    ));
    // Ветка `return` необязательна: без неё значение вычисления и есть ответ.
    program(&format!(
        "{}
run : Bool
run = handle program with
  get -> resume True
  put x -> resume MkUnit
",
        effects()
    ));
    // Остаток непуст: `Log` хендлер не трогает, и он остаётся окружающей.
    program(&format!(
        "{}
both : {{Log, State Bool}} Bool
both u =
  note True
  get

outer : {{Log}} Bool
outer u = handle both with
  return v -> v
  get -> resume True
  put x -> resume MkUnit
",
        effects()
    ));
}

#[test]
fn a_written_label_pins_the_occurrence_it_removes() {
    // §3.4: `@`-аннотация правила не меняет - снимается всё то же первое
    // (внутреннее) вхождение, - а говорит, чем обязаны оказаться его аргументы.
    // Выбирать вхождение она не может: элиминатор ставит снимаемую метку первой
    // в своём домене, а порядок внутри группы одноимённых значим.
    let head = format!(
        "{}
both : {{State Nat, State Bool}} Bool
both u =
  put True
  get
",
        effects()
    );
    program(&format!(
        "{head}
inner : {{State Bool}} Bool
inner u = handle @(State Nat) both with
  get -> resume Zero
  put x -> resume MkUnit
"
    ));
    for (written, why) in [
        ("@(State Bool)", "первое вхождение"),
        ("@Bool", "обязана быть эффектом"),
        ("@Log", "такой операции у эффекта нет"),
    ] {
        let error = refused(&format!(
            "{head}
inner : {{State Bool}} Bool
inner u = handle {written} both with
  get -> resume Zero
  put x -> resume MkUnit
"
        ));
        assert!(error.to_string().contains(why), "получено {error:?}");
    }
}

#[test]
fn a_single_shot_resumption_is_affine() {
    // Различие single-shot и multi-shot выражено не отдельным механизмом, а
    // линейностью (§3.3): `resume` при `handle` аффинна, при `handleMulti` -
    // неограниченна. Забыть её законно - ветка, не зовущая её, обрывает
    // вычисление.
    let twice = "
run : Bool
run = handle program with
  return v -> v
  get -> resume (resume True)
  put x -> resume MkUnit
";
    let error = refused(&format!("{}{twice}", effects()));
    assert!(
        error.to_string().contains("кратностью 1"),
        "получено {error:?}"
    );
    program(&format!(
        "{}{}",
        effects(),
        twice.replace("handle program", "handleMulti program")
    ));
    // Не позвать её - законно.
    program(&format!(
        "{}
run : Bool
run = handle program with
  return v -> v
  get -> False
  put x -> True
",
        effects()
    ));
}

#[test]
fn a_handler_covers_its_effect_exactly() {
    // Полнота веток следует из арности элиминатора, а не из отдельной
    // проверки: у каждой операции своё связывание.
    for (written, why) in [
        ("  return v -> v\n  get -> resume True\n", "не написана"),
        (
            "  return v -> v\n  get -> resume True\n  get -> resume False\n  put x -> resume MkUnit\n",
            "дважды",
        ),
        (
            "  return v -> v\n  get -> resume True\n  put x -> resume MkUnit\n  note b -> resume MkUnit\n",
            "такой операции у эффекта нет",
        ),
    ] {
        let error = refused(&format!(
            "{}
run : Bool
run = handle program with
{written}",
            effects()
        ));
        assert!(error.to_string().contains(why), "получено {error:?}");
    }
    // Под хендлером обязано стоять вычисление, производящее метку.
    let error = refused(&format!(
        "{}
run : Bool
run = handle True with
  return v -> v
  get -> resume True
  put x -> resume MkUnit
",
        effects()
    ));
    assert!(
        error.to_string().contains("обязано стоять вычисление"),
        "получено {error:?}"
    );
}

#[test]
fn a_constructor_field_carries_no_row_tail() {
    // Подъём у конструктора выключен намеренно (§3.4): стрелки его - не позиции
    // сигнатуры, а форма самого значения, и открытая row у поля означала бы,
    // что два значения с разными эффектами дают один тип. Написанный руками
    // хвост проходил мимо этого запрета - `free_in` хвост эффектной row не
    // собирает, его связывает `named_tail`, - и обобщение делало конструктор
    // row-полиморфным при row-арности семейства нуль. Тип получался тихо
    // неверный: номер параметра зависел от того, какое поле тронуло тело, а
    // законная программа, зовущая оба, отвергалась с чужим именем в сообщении.
    let text = "\
data Bool where
  True : Bool

data Unit where
  MkUnit : Unit

effect State s where
  put : s -> Unit
";
    let error = refused(&format!(
        "{text}
data Cell where
  MkCell : (Bool -> {{State Bool | e}} Unit) -> Cell
"
    ));
    assert!(
        matches!(error, ElabError::ConstructorRow { .. }),
        "получено {error:?}"
    );
    // Замкнутый набор меток у поля законен и работает: пустую row вызываемого
    // гасит любая окружающая, а эта объявлена.
    program(&format!(
        "{text}
data Cell where
  MkCell : (Bool -> {{State Bool}} Unit) -> (Bool -> {{State Bool}} Unit) -> Cell

both : Cell -> Bool -> {{State Bool}} Unit
both (MkCell g h) b =
  g b
  h b
"
    ));
}

#[test]
fn a_group_member_instantiates_its_neighbour_row_afresh() {
    // Правило одно на оба сорта параметров (§10 вопросы 54 и 73): свой -
    // переменная, чужой - дырка, потому что сосед объявляется рядом, но
    // инстанцируется в каждом месте использования заново. Для уровней оно
    // соблюдалось, для row - только на словах: список аргументов был пуст, то
    // есть подстановка тождественна, и параметры соседа читались как свои.
    // Отказ называл переменную, которой в области видимости нет, а те же два
    // определения подряд проходили - обёртка в `mutual` снова отнимала.
    let text = "\
data Bool where
  True : Bool

data Unit where
  MkUnit : Unit

effect State s where
  put : s -> Unit
";
    program(&format!(
        "{text}
mutual
  f : Bool -> Bool -> {{State Bool | e}} Bool
  f a b = a

  g : Bool -> {{State Bool | e}} Bool
  g a = f a a
"
    ));
    // Тот же текст без группы обязан проходить - иначе тест ловил бы не то.
    program(&format!(
        "{text}
f : Bool -> Bool -> {{State Bool | e}} Bool
f a b = a

g : Bool -> {{State Bool | e}} Bool
g a = f a a
"
    ));
}

#[test]
fn a_field_of_a_branch_carries_the_multiplicity_of_the_scrutinee() {
    // §3.3 дословно: «поле, связанное при `qᵢ·r`, разобранное в свою очередь,
    // даёт `r' = qᵢ·r`». Ядро так и делает, элаборация брала `qᵢ` как есть, и
    // вложенный разбор давал полю `1` там, где ядро дало `ω`. Расхождение
    // всегда в строгую сторону, поэтому это false-rejection, а не unsoundness -
    // но отвергалась `case`-версия программы, которую клаузами написать можно,
    // и сообщение называло безымянное `_`, которого автор не писал.
    let text = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

g : Nat -> Nat -> Nat
g a b = a
";
    program(&format!(
        "{text}
deepClause : Nat -> Nat
deepClause Zero = Zero
deepClause (Succ Zero) = Zero
deepClause (Succ (Succ m)) = g m m

deepCase : Nat -> Nat
deepCase n = case n of
  Zero -> Zero
  Succ k -> case k of
    Zero -> Zero
    Succ m -> g m m
"
    ));
    // Направление проверки: линейное поле дважды по-прежнему отказ, и по обоим
    // путям одинаково.
    let linear = "\
data Bool where
  True : Bool
  False : Bool

close : (1 b : Bool) -> Bool
close b = True

resource File where
  Open : Bool -> File
  shut : (1 h : File) -> Bool
  shut (Open b) = close b

both : Bool -> Bool -> Bool
both a b = a
";
    for body in [
        "twice : (1 s : File) -> Bool\ntwice s = case s of\n  Open b -> both (close b) (close b)\n",
        "twice : (1 s : File) -> Bool\ntwice (Open b) = both (close b) (close b)\n",
    ] {
        let error = refused(&format!("{linear}\n{body}"));
        assert!(
            error.to_string().contains("использована"),
            "{body}: получено {error:?}"
        );
    }
}

#[test]
fn a_case_over_a_written_index_typechecks() {
    // Цель разбора заводилась дыркой по **всему** контексту, включая только
    // что связанное разбираемое, а мотив переписывает разбираемое в собственное
    // связывание, индексов не трогая. Дырка после этого не типизировалась, и
    // ломалось это на всяком индексе, который не голая переменная: `case v of
    // Nil -> True` над `Vect Zero` отвечало «ожидался `Vect Zero`, получен
    // `Vect #1`», а побуквенно та же клауза проходила. Канонический `head`
    // через `case` не писался вовсе.
    program(
        "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Vect : Nat -> Type where
  Nil : Vect Zero
  Cons : (0 n : Nat) -> Bool -> Vect n -> Vect (Succ n)

emptyClause : Vect Zero -> Bool
emptyClause Nil = True

emptyCase : Vect Zero -> Bool
emptyCase v = case v of
  Nil -> True

headClause : (0 n : Nat) -> Vect (Succ n) -> Bool
headClause n (Cons k x xs) = x

headCase : (0 n : Nat) -> Vect (Succ n) -> Bool
headCase n v = case v of
  Cons k x xs -> x
",
    );
}

#[test]
fn a_callback_with_fewer_effects_is_passed_as_is() {
    // §3.4 разводит равенство и унификацию: второе сопоставляет метки по имени,
    // а **остаток уходит в хвостовую метапеременную**. Реализовано было первое,
    // и решатель хвоста писал решение всегда без меток - поэтому `withLog
    // pure1` отвергалось, хотя решение `?m := {Log | e}` единственно. Обходилось
    // η-развёрткой, то есть higher-order-передача, которую §3.4 приводит
    // мотивом правила погашения, не писалась.
    let base = "\
data Bool where
  True : Bool

data Unit where
  MkUnit : Unit

effect Log where
  note : Bool -> Unit

effect Tick where
  tick : Unit

withLog : (Bool -> {Log} Bool) -> {Log} Bool
withLog f = f True
";
    program(&format!(
        "{base}
pure1 : Bool -> Bool
pure1 b = b

got : {{Log}} Bool
got u = withLog pure1
"
    ));
    // Направление одностороннее: у колбэка, производящего **своё**, остаток
    // непуст с обеих сторон, и это §10 вопрос 80 - отказ, а не догадка.
    let error = refused(&format!(
        "{base}
noisy : Bool -> {{Tick}} Bool
noisy b = b

got : {{Log}} Bool
got u = withLog noisy
"
    ));
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_branch_works_in_the_ambient_of_its_handle() {
    // §3.4: «собственные эффекты веток гасятся окружающей по тому же правилу
    // расширения», и окружающая тела ветки - окружающая **применения**
    // `handle`, а не остаток вычисления. Пока обе роли играла ρ, ветка могла
    // производить только то, что осталось в вычислении, и хендлер-трансформер
    // `mapS` - приведённый §3.4 мотивом самого правила погашения - не
    // типизировался.
    let base = "\
data Bool where
  True : Bool

data Unit where
  MkUnit : Unit

effect Tick where
  tick : Unit

effect Log where
  note : Bool -> Unit
";
    // Ветка производит эффект, которого у вычисления нет вовсе.
    program(&format!(
        "{base}
prod : {{Tick}} Bool
prod u = True

transform : {{Log}} Bool
transform u = handle prod with
  return v -> v
  tick -> resume (note True)
"
    ));
    // Остаток вычисления при этом обязан всплывать по-прежнему - и тогда,
    // когда ветка резюмирует, и тогда, когда обрывает: до первой операции
    // вычисление успевает сделать своё.
    for branch in ["resume MkUnit", "True"] {
        let leaks = format!(
            "{base}
prod : {{Tick, Log}} Bool
prod u =
  note True
  tick
  True

escapes : Bool
escapes = handle prod with
  return v -> v
  tick -> {branch}
"
        );
        let error = refused(&leaks);
        assert!(
            error.to_string().contains("не погашены"),
            "{branch}: получено {error:?}"
        );
        // Та же программа с объявленным остатком проходит.
        program(
            &leaks
                .replace("escapes : Bool", "escapes : {Log} Bool")
                .replace("escapes = handle prod with", "escapes u = handle prod with"),
        );
    }
}

#[test]
fn an_effect_declares_its_eliminators() {
    // §3.4: `handle e with …` есть применение константы, а не узел ядра.
    // Объявление заводит две - одношотную и мультишотную, - и различает их
    // только кратность резумпции.
    let signature = program(&format!(
        "{BASE}
data Unit where
  MkUnit : Unit

effect State s where
  get : s
  put : s -> Unit
"
    ));
    for name in ["#handle.State", "#handleMulti.State"] {
        let handler = signature.lookup(name).expect("элиминатор объявлен");
        // Параметров-row два, и роли у них разные (§3.4). ρ - остаток
        // вычисления, глубина хендлера: её несут `resume` и стрелки спайна,
        // потому что остаток производится и тогда, когда ветка обрывает. λ -
        // окружающая применения: её несут тела веток, потому что ветка
        // выполняется там, где написан сам хендлер. Совпадать они не обязаны -
        // на этом стоит хендлер-трансформер.
        assert_eq!(handler.row_arity, 2, "{name}");
        // Связывания: параметр метки, `a`, `b`, вычисление, `return` и по
        // ветке на операцию.
        assert_eq!(binders(&handler.ty), 1 + 2 + 1 + 1 + 2, "{name}");
        // Постулат: развернуть его нечем, пока evidence не подставлен.
        assert!(handler.body.is_none(), "{name}");
    }
    // Резумпция аффинна у `handle` и неограниченна у `handleMulti` - это и
    // есть single-shot против multi-shot (§3.3).
    let one = &signature.lookup("#handle.State").expect("объявлен").ty;
    let many = &signature.lookup("#handleMulti.State").expect("объявлен").ty;
    assert_ne!(one.to_string(), many.to_string());
    assert_eq!(
        one.to_string().replace("(1 resume", "(ω resume"),
        many.to_string()
    );
}

#[test]
fn an_operation_may_have_parameters_of_its_own() {
    // §4.4 пишет `throw : e -> {Except e} a` - каноническую обрывающую
    // операцию. Своих параметров операции не полагалось: арность уровня
    // сверялась с арностью метки равенством, скопированным у конструктора. Довод
    // конструктора («элиминация инстанцирует его теми же аргументами, что и
    // семейство») к операции не относится - её инстанцирует место вызова, - и
    // §4.4 не писалась ни в одну из двух записей: явную `{a : Type} -> e -> a`
    // отвергала арность, а свободное имя не обобщалось вовсе.
    let text = "\
data Bool where
  True : Bool
  False : Bool

data Unit where
  MkUnit : Unit

effect Except e where
  throw : e -> a

guard : Bool -> {Except Bool} Bool
guard True = True
guard False = throw False
";
    let signature = program(text);
    // Параметры метки у операции первыми, свои - следом. Метка полиморфна по
    // одному уровню, операция по двум: своему `a` и её.
    let former = signature.lookup("Except").expect("метка объявлена");
    let throw = signature.lookup("throw").expect("операция объявлена");
    assert_eq!(former.level_arity, 1);
    assert_eq!(throw.level_arity, 2);

    // Явная запись того же - та же арность.
    let explicit = program(&text.replace("throw : e -> a", "throw : {a : Type} -> e -> a"));
    assert_eq!(explicit.lookup("throw").expect("объявлена").level_arity, 2);

    // Ветка связывает поднятое `a` наравне с написанными аргументами: без
    // вставки первый написанный параметр встал бы на его место, и `throw x -> x`
    // получало бы `x : Type`.
    program(&format!(
        "{text}
risky : {{Except Bool}} Bool
risky u = guard False

caught : Bool
caught = handle risky with
  return v -> v
  throw x -> x
"
    ));
}

#[test]
fn a_polymorphic_operation_is_handled_at_a_single_level() {
    // Уровень поднятого параметра операции связать нечем: ветка по нему
    // полиморфна, метка о нём не несёт ничего, тип вычисления его не называет.
    // Свежая дырка на этом месте оставалась бы нерешённой навсегда, и хендлер,
    // чья ветка не зовёт `resume`, отвергался бы всегда - то есть ровно `try`
    // из §4.4. Берётся нуль; аргумент стёрт, и ветка обращается с ним
    // параметрически.
    let signature = program(
        "\
data Bool where
  True : Bool
  False : Bool

data Unit where
  MkUnit : Unit

effect Amb where
  pick : a -> a -> a

both : {Amb} Bool
both u = pick True False

first : Bool
first = handle both with
  return v -> v
  pick x y -> resume x
",
    );
    // Уровней у элиминатора три: параметров метки нет вовсе, два несут
    // результат вычисления и ответ хендлера, третий принесла операция.
    let handler = signature
        .lookup("#handle.Amb")
        .expect("элиминатор объявлен");
    assert_eq!(handler.level_arity, 3);
    // Ветка зовёт резумпцию, и `a` определяется её аргументом - уровень при
    // этом остаётся тем, что подставило применение.
    let body = signature
        .lookup("first")
        .expect("определено")
        .body
        .as_ref()
        .expect("тело есть");
    assert!(body.to_string().contains("#handle.Amb"), "получено {body}");
}

/// Сколько связываний у спайна типа.
fn binders(ty: &Term) -> usize {
    let mut found = 0;
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        found += 1;
        current = codomain;
    }
    found
}
