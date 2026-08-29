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
        ("f : a -> a\n", Missing::Implicits),
        ("f : {a : Type} -> Nat\n", Missing::ImplicitBinder),
        ("f : Nat -> Nat\nf x = x @Nat\n", Missing::TypeApplication),
        ("f : Nat -> Nat\nf x = _\n", Missing::TermHole),
        ("f : Nat -> Nat\nf x = 1\n", Missing::Literal),
        ("f : Nat\nf =\n  let x = Zero\n  x\n", Missing::UntypedLet),
        (
            "f : Nat -> Nat\nf = \\(0 x : Nat) -> x\n",
            Missing::LambdaAnnotation,
        ),
        (
            "f : Nat -> Nat\nf x = if x then x else x\n",
            Missing::Conditional,
        ),
        (
            "f : Nat -> Nat\nf x = case x of\n  Zero -> Zero\n",
            Missing::CaseExpression,
        ),
        ("f : Nat\nf = (Zero, Zero)\n", Missing::Tuple),
        ("f : Nat\nf = ()\n", Missing::Unit),
        ("f : Nat\nf = [Zero]\n", Missing::List),
        ("f : Nat\nf = Zero + Zero + Zero\n", Missing::Fixities),
        (
            "data Pair a b where\n  MkPair : Nat\n",
            Missing::FamilyParameters,
        ),
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
fn a_free_type_variable_is_refused_for_now() {
    // Полиморфизм упирается в ядро, а не в элаборацию: подъём `a` в
    // implicit-параметр требует видимости у `Pi` и метапеременных на термах.
    let error = refused("f : a -> a\n");
    let ElabError::Missing {
        what: Missing::Implicits,
        ..
    } = error
    else {
        panic!("ожидались имплиситы, получено {error:?}");
    };
    // В теле то же имя - опечатка, а не свободная переменная: поднимать в
    // implicit-параметр там нечего.
    let error = refused(&format!("{BASE}f : Nat -> Nat\nf n = a\n"));
    assert!(
        matches!(error, ElabError::UnknownName { .. }),
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
