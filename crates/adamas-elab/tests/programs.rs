//! Программы Adamas от текста до проверки типов - milestone Фазы 2.
//!
//! Проверяется не форма собранного терма, а два факта: программа доходит до
//! сигнатуры и то, что в ней оказалось, **вычисляет то, что написано**.
//! Форма - деталь элаборации, и тест на неё ломался бы от смены стратегии,
//! ничего при этом не защищая.

use std::rc::Rc;

use adamas_core::check::{ErrorKind, check_closed};
use adamas_core::level::Level;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
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
    Term::Const(name.into(), Rc::from([Level::Zero]))
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
        let family = at("P").apply([Term::constant("plus").apply([number(left), number(right)])]);
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
        let stated = at("Q").apply([Term::constant("even").apply([number])]);
        let outcome = check_closed(&signature, &witness, &stated);
        assert!(outcome.is_ok(), "even {input} = {expected}: {outcome:?}");
    }
    // `_` связывает, ничего не называя: тело обязано считаться так же, как
    // если бы аргумента не было вовсе.
    let witness = at("q").apply([Term::constant("True")]);
    let stated = at("Q").apply([Term::constant("constant").apply([Term::constant("Zero")])]);
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
    let stated = at("P").apply([Term::constant("+").apply([number(1), number(2)])]);
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
        ("f : Nat\nf =\n  Zero\n  Zero\n", Missing::Sequencing),
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
    let one = Term::constant("one");
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
        &at("P").apply([Term::constant("written")]),
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
        &at("P").apply([Term::constant("f")]),
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
        &at("P").apply([Term::constant("two")]),
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
            &at("P").apply([Term::constant("pred").apply([number(input)])]),
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
        &at("P").apply([Term::constant("pick").apply([Term::constant("True")])]),
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
    // Полнота приходит от того же компилятора, а поднятые колонки контекста в
    // примере не показываются: автор их не писал.
    let error = refused(&format!(
        "{BASE}f : Nat -> Bool\nf n = case n of\n  Zero -> True\n"
    ));
    let ElabError::Clauses { error, .. } = error else {
        panic!("ожидалась сборка клауз, получено {error:?}");
    };
    assert_eq!(error.to_string(), "не покрыто: `(Succ _)`");
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
        &at("P").apply([
            Term::constant("sum").apply([Term::constant("mk").apply([number(1), number(2)])])
        ]),
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
        let projected = Term::Project(
            Rc::new(Term::constant("moved").apply([Term::constant("start")])),
            field.into(),
        );
        let outcome = check_closed(
            &signature,
            &at("anything").apply([number(expected)]),
            &at("P").apply([projected]),
        );
        assert!(outcome.is_ok(), "поле {field}: {outcome:?}");
    }
    // Расширение дописывает поле, не трогая прежние.
    let promoted = Term::constant("promote").apply([Term::constant("start"), number(2)]);
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
fn a_mutual_group_carries_definitions_only() {
    // Названные границы: постулат группой объявлять незачем - он и есть
    // отсутствие тела, - а семейство в группе требует смешанной группы, и
    // это отдельный срез.
    for text in [
        "mutual\n  loose : Nat\n",
        "mutual\n  data Tree where\n    Leaf : Tree\n",
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
