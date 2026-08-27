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
fn a_resource_without_a_destructor_is_refused() {
    let text = format!("{BASE}\nresource File where\n  Open : Bool -> File\n");
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::ResourceWithoutDrop { .. }),
        "получено {error:?}"
    );
}

#[test]
fn a_resource_body_defines_only_its_destructor() {
    // Тело держит конструкторы и `drop`; всё прочее определяется рядом.
    let text = format!(
        "{BASE}
resource File where
  Open : Bool -> File
  helper : Bool -> Bool
  helper b = b
"
    );
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::ResourceMember { .. }),
        "получено {error:?}"
    );
}
