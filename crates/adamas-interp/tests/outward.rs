//! Машина наружу: чужой символ настоящей библиотеки (§5.3, §10 вопрос 182).
//!
//! Пробная правка трека C волны 1 Фазы 8 под вариант (а) вопроса 182. Свидетели
//! отвечают на два вопроса: **ходит ли машина наружу по-настоящему** и **как
//! ведёт себя каждая из названных опасностей**.
//!
//! Путь идёт в обход поверхностного языка: слова `extern` в грамматике нет, и
//! заводит его трек B. Имя объявляется постулатом, а чужой символ ставится за
//! ним [`Machine::declare_foreign`]. Постулат, а не определение, потому что тело
//! развернулось бы δ-шагом раньше, чем машина дошла бы до внешнего вызова.
//!
//! # Выбор символа
//!
//! `cbrt` из `libm.so.6`, и выбор этот сделан тремя доводами, а не удобством.
//!
//! *Библиотека заведомо есть.* glibc 2.42 в dev-окружении держит `libm.so.6`
//! отдельным файлом, и `dlopen` его берёт по имени без пути; `cbrt` при этом
//! **нет** ни в `libc.so.6`, ни в глобальной области процесса (`dlopen(NULL)`),
//! то есть символ приходит именно из загруженной библиотеки, а не оказывается
//! под рукой сам собой.
//!
//! *Сигнатура тривиальна и при этом не пуста:* `double -> double` - плоское
//! значение полной ширины в обе стороны, ровно то, что трек A назвал единственным
//! видом, который сегодня переходит границу.
//!
//! *Ответ невозможно подделать.* `cbrt(27.0)` в glibc есть
//! `3.0000000000000004`, а не `3.0`: корректно округлённый ответ отличается на
//! один ULP. Свидетель, сравнивающий с `f64::cbrt` (тот же символ той же
//! библиотеки), поэтому краснеет от всякой подмены вызова счётом - в том числе
//! от свёртки константы сишным компилятором, которая даёт ровно `3.0`
//! (`adamas-codegen/tests/outward.rs`).
//!
//! Рядом стоят `labs` из `libc.so.6` - целый регистр вместо SSE и **вторая**
//! библиотека в таблице - и `pow` - два аргумента.
//!
//! # Мутанты, которыми это мерено (2026-09-20)
//!
//! Таблица снята прогоном `cargo test -p adamas-interp --test outward` на каждой
//! правке порознь, с возвратом между ними. Счёт - упавших свидетелей из девяти;
//! контроль на чистом дереве - ноль. Таблица целиком - в
//! `docs/phase8-trackC-notes.md`.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

use std::rc::Rc;

use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::prim::{Prim, PrimTy};
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Binder, Term};
use adamas_core::value::Env;

use adamas_interp::{Foreign, Linkage, Machine, RunError};

/// Математическая библиотека glibc.
const LIBM: &str = "libm.so.6";
/// Библиотека C.
const LIBC: &str = "libc.so.6";

/// Литерал `Float64` термом.
fn literal(value: f64) -> Term {
    Term::Prim(Prim::literal(PrimTy::Float64, value.to_bits()))
}

/// Сигнатура с постулатом названной арности над плоскими типами.
fn postulated(name: &str, params: &[PrimTy], result: PrimTy) -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let ty = params
        .iter()
        .rev()
        .fold(Term::Prim(Prim::Ty(result)), |codomain, param| {
            Term::Pi(
                Binder::explicit(Mult::Many),
                "x".into(),
                Rc::new(Term::Prim(Prim::Ty(*param))),
                Row::empty(),
                Rc::new(codomain),
            )
        });
    signature
        .postulate(&mut metas, name, Mult::Many, 0, ty)
        .expect("постулат обязан объявляться");
    signature
}

/// Прогон терма машиной, за именем которой стоит чужой символ.
///
/// Читается ответ обратно в терм - ровно тем путём, каким печатает его
/// `adamas eval`: свидетель обязан смотреть на то, что увидит человек.
fn ran(signature: &Signature, name: &str, it: Foreign, term: &Term) -> Result<Term, RunError> {
    let mut machine = Machine::new(signature);
    machine.declare_foreign(name, it);
    let value = machine.evaluate(&Env::default(), term)?;
    machine.read(value)
}

/// Биты `Float64` из прочитанного терма.
fn bits(term: &Term) -> u64 {
    match term {
        Term::Prim(Prim::Lit(PrimTy::Float64, bits)) => *bits,
        other => panic!("ответ не литерал `Float64`: {}", other.printed(None)),
    }
}

/// Ответ машины на `cbrt x` для одного аргумента.
fn cube_root(input: f64) -> Term {
    let signature = postulated("cbrt", &[PrimTy::Float64], PrimTy::Float64);
    let it = Foreign::new(LIBM, "cbrt", &[PrimTy::Float64], PrimTy::Float64);
    ran(
        &signature,
        "cbrt",
        it,
        &Term::constant("cbrt").apply([literal(input)]),
    )
    .expect("вызов обязан проходить")
}

/// Аргумент, спрятанный за именем, разворачивается до вызова.
///
/// Свидетель того, что чужой вызов разворачивает живые аргументы тем же
/// правилом, каким их разворачивает примитивная операция ядра: свёртке нужен
/// литерал, а имя с телом само до него не разворачивается. Без разворота
/// `cbrt thousand` застревал бы там, где `cbrt 1000.0` считается, - то есть
/// программа зависела бы от того, написан аргумент числом или именем.
///
/// Заведён свидетель мутантом: пока его не было, правка «не звать `forced`»
/// не роняла ни одного из одиннадцати.
#[test]
fn an_argument_behind_a_definition_is_unfolded_first() {
    let mut signature = postulated("cbrt", &[PrimTy::Float64], PrimTy::Float64);
    let mut metas = Metas::default();
    signature
        .define(
            &mut metas,
            "thousand",
            Mult::Many,
            0,
            Term::Prim(Prim::Ty(PrimTy::Float64)),
            Some(literal(1000.0)),
        )
        .expect("определение обязано объявляться");
    let it = Foreign::new(LIBM, "cbrt", &[PrimTy::Float64], PrimTy::Float64);
    let answer = ran(
        &signature,
        "cbrt",
        it,
        &Term::constant("cbrt").apply([Term::constant("thousand")]),
    )
    .expect("вызов обязан проходить");
    assert_eq!(
        bits(&answer),
        10.0_f64.to_bits(),
        "аргумент за именем не развернулся: чужой вызов застрял"
    );
}

/// Машина зовёт настоящий `cbrt` настоящей `libm.so.6` и отвечает как он.
///
/// Аргументы - точные кубы, и это не удобство: на них ответ один у всякой
/// реализации `cbrt`, поэтому свидетель говорит о **нашем пути**, а не о том,
/// какая libm нашлась. Отрицательный стоит рядом с положительным, потому что
/// знак у кубического корня - отдельная ветвь всякой реализации.
///
/// Что путь идёт именно в `libm.so.6`, а не куда-нибудь ещё, предъявляет
/// соседний свидетель ([`the_answer_comes_from_glibc_and_not_from_rust`]).
#[test]
fn the_machine_calls_a_real_symbol_of_a_real_library() {
    assert_eq!(
        bits(&cube_root(1000.0)),
        10.0_f64.to_bits(),
        "куб 1000 дал не 10"
    );
    assert_eq!(
        bits(&cube_root(-125.0)),
        (-5.0_f64).to_bits(),
        "куб -125 дал не -5"
    );
}

/// Ответ приходит из glibc, а не из реализации, вшитой в сам компилятор.
///
/// Свидетель измеренного факта, без которого вся сверка трёх вычислителей
/// читалась бы неверно: **`cbrt` в одном процессе не один**. Rust линкует
/// собственный (`compiler_builtins::math::libm_math::cbrt`) и `libm.so.6` не
/// подключает вовсе - `ldd` над тестовым бинарём её не называет, - а
/// `27.0_f64.cbrt()` даёт корректно округлённое `3.0`. glibc на том же
/// аргументе даёт `3.0000000000000004`, то есть на один ULP больше.
///
/// Отсюда правило, которое трек C обязан назвать: «правильный ответ» чужой
/// функции есть свойство **названной библиотеки**, а не имени символа. Сверять
/// машину с `f64::cbrt` значило бы сверять её с другой реализацией.
///
/// Свидетель предъявляет расхождение, а не оговаривает его. Сойдись две
/// реализации - он покраснеет, и это правильно: утверждение об окружении, на
/// котором стоят выводы трека, обязано пересчитываться вместе с окружением.
#[test]
fn the_answer_comes_from_glibc_and_not_from_rust() {
    let ours = bits(&cube_root(27.0));
    assert_ne!(
        ours,
        27.0_f64.cbrt().to_bits(),
        "libm glibc и libm компилятора сошлись: вывод трека о двух реализациях пора пересчитать"
    );
    // Разойтись им позволено на один ULP, а не на сколько угодно: иначе
    // свидетель зеленел бы и от совсем чужого числа.
    let ulps = ours.abs_diff(3.0_f64.to_bits());
    assert_eq!(ulps, 1, "расхождение не в один ULP, а в {ulps}");
}

/// Вторая библиотека и целый регистр вместо SSE: `labs` из `libc.so.6`.
///
/// Нужен двум утверждениям сразу. Таблица загруженных держит **больше одной**
/// библиотеки - с одной записью промах по ключу был бы ненаблюдаем. И класс
/// регистра у аргумента другой: `double` едет в SSE, `long` - в целом, и ветвь
/// диспетчера у них разная.
#[test]
fn a_second_library_and_the_integer_register_take_the_same_path() {
    let signature = postulated("labs", &[PrimTy::Int64], PrimTy::Int64);
    let it = Foreign::new(LIBC, "labs", &[PrimTy::Int64], PrimTy::Int64);
    let answer = ran(
        &signature,
        "labs",
        it,
        &Term::constant("labs").apply([Term::Prim(Prim::literal(
            PrimTy::Int64,
            // Дополнительный код: биты литерала ядра хранятся так же, а
            // `cast_unsigned` на `i64` требует 1.87 при MSRV 1.85.
            1_234_567_u64.wrapping_neg(),
        ))]),
    )
    .expect("вызов обязан проходить");
    assert_eq!(
        answer,
        Term::Prim(Prim::literal(PrimTy::Int64, 1_234_567)),
        "`labs` ответил не модуль"
    );
}

/// Два аргумента переходят границу: `pow(2.0, 10.0)`.
///
/// Ответ выбран точным в двоичной плавающей арифметике намеренно: неточный
/// здесь сравнивался бы с `f64::powf`, а тот вправе быть не тем же символом.
#[test]
fn two_arguments_cross_the_boundary() {
    let signature = postulated("pow", &[PrimTy::Float64, PrimTy::Float64], PrimTy::Float64);
    let it = Foreign::new(
        LIBM,
        "pow",
        &[PrimTy::Float64, PrimTy::Float64],
        PrimTy::Float64,
    );
    let answer = ran(
        &signature,
        "pow",
        it,
        &Term::constant("pow").apply([literal(2.0), literal(10.0)]),
    )
    .expect("вызов обязан проходить");
    assert_eq!(bits(&answer), 1024.0_f64.to_bits(), "`pow` ответил не 1024");
}

/// Отсутствующая библиотека - отказ с текстом, а не паника.
///
/// Текст `dlopen` пересказывается дословно, потому что он и называет причину;
/// сверяется здесь то, что отказ **называет имя** - без него автор пошёл бы
/// искать не ту библиотеку.
#[test]
fn a_missing_library_is_a_refusal_with_a_name() {
    let signature = postulated("nope", &[PrimTy::Float64], PrimTy::Float64);
    let it = Foreign::new(
        "libnosuchthing.so.999",
        "cbrt",
        &[PrimTy::Float64],
        PrimTy::Float64,
    );
    let error = ran(
        &signature,
        "nope",
        it,
        &Term::constant("nope").apply([literal(27.0)]),
    )
    .expect_err("отсутствующая библиотека обязана быть отказом");
    let text = error.to_string();
    assert!(
        matches!(error, RunError::NoLibrary { .. }),
        "отказ не тот: {text}"
    );
    assert!(
        text.contains("libnosuchthing.so.999"),
        "отказ не назвал библиотеку: {text}"
    );
}

/// Отсутствующий символ - свой отказ, называющий и библиотеку, и имя.
///
/// Отдельно от отсутствующей библиотеки намеренно: «нет файла» и «файл есть,
/// имени в нём нет» чинятся по-разному.
#[test]
fn a_missing_symbol_names_both_the_library_and_the_symbol() {
    let signature = postulated("nope", &[PrimTy::Float64], PrimTy::Float64);
    let it = Foreign::new(LIBM, "cbrt_xyzzy", &[PrimTy::Float64], PrimTy::Float64);
    let error = ran(
        &signature,
        "nope",
        it,
        &Term::constant("nope").apply([literal(27.0)]),
    )
    .expect_err("отсутствующий символ обязан быть отказом");
    let text = error.to_string();
    assert!(
        matches!(error, RunError::NoSymbol { .. }),
        "отказ не тот: {text}"
    );
    assert!(
        text.contains(LIBM) && text.contains("cbrt_xyzzy"),
        "отказ не назвал, где и что искали: {text}"
    );
}

/// Сигнатура вне таблицы вызова - отказ, а не догадка.
///
/// `Float32` через границу сегодня не ходит: звать по нетипизированному адресу
/// можно только **точной** сигнатурой, а узкий тип в регистре старшими битами
/// не определён. Отказ называет сигнатуру целиком - без неё непонятно, какая из
/// позиций не подошла.
#[test]
fn a_signature_outside_the_table_is_refused_by_name() {
    let signature = postulated("cbrtf", &[PrimTy::Float32], PrimTy::Float32);
    let it = Foreign::new(LIBM, "cbrtf", &[PrimTy::Float32], PrimTy::Float32);
    let error = ran(
        &signature,
        "cbrtf",
        it,
        &Term::constant("cbrtf").apply([Term::Prim(Prim::literal(
            PrimTy::Float32,
            u64::from(1.0_f32.to_bits()),
        ))]),
    )
    .expect_err("форма вне таблицы обязана быть отказом");
    let text = error.to_string();
    assert!(
        matches!(error, RunError::ForeignShape { .. }),
        "отказ не тот: {text}"
    );
    assert!(
        text.contains("(Float32) -> Float32"),
        "отказ не назвал сигнатуру: {text}"
    );
}

/// Недобранное чужое имя застревает, как всякая нейтраль, и наружу не ходит.
///
/// Это нормальный, а не опасный случай: частичное применение чужой функции -
/// обычное значение, и отказывать на нём значило бы отказывать раньше, чем
/// программа что-то попросила. Наблюдается застревание тем, что ответ есть сам
/// терм применения.
#[test]
fn an_underapplied_foreign_name_stays_stuck() {
    let signature = postulated("pow", &[PrimTy::Float64, PrimTy::Float64], PrimTy::Float64);
    let it = Foreign::new(
        LIBM,
        "pow",
        &[PrimTy::Float64, PrimTy::Float64],
        PrimTy::Float64,
    );
    let answer = ran(
        &signature,
        "pow",
        it,
        &Term::constant("pow").apply([literal(2.0)]),
    )
    .expect("недобор обязан быть значением, а не отказом");
    assert_eq!(
        answer.printed(None).to_string(),
        "pow 2.0",
        "недобранное применение не осталось собой"
    );
}

/// Литерал не того типа, каким объявлен аргумент, - отказ, а не расширение.
///
/// Догадка здесь была бы хуже отказа: расширять `UInt64` до `Float64` можно
/// преобразованием значения и перекладкой битов, и выбор принадлежит
/// объявлению, а не машине.
#[test]
fn a_literal_of_the_wrong_type_is_refused() {
    let signature = postulated("cbrt", &[PrimTy::Float64], PrimTy::Float64);
    let it = Foreign::new(LIBM, "cbrt", &[PrimTy::Float64], PrimTy::Float64);
    let error = ran(
        &signature,
        "cbrt",
        it,
        &Term::constant("cbrt").apply([Term::Prim(Prim::literal(PrimTy::UInt64, 27))]),
    )
    .expect_err("литерал не того типа обязан быть отказом");
    let text = error.to_string();
    assert!(
        matches!(error, RunError::ForeignArgument { .. }),
        "отказ не тот: {text}"
    );
    assert!(
        text.contains("Float64") && text.contains("UInt64"),
        "отказ не назвал ни объявленного, ни пришедшего: {text}"
    );
}

/// Объявленная арность больше настоящей - и **этого не ловит ничто**.
///
/// Главная опасность варианта (а), предъявленная прогоном, а не оговоркой.
/// `dlsym` отдаёт адрес без типа; сверить объявленную сигнатуру с настоящей
/// нечем ни машине, ни компоновщику, ни загрузчику. Объявив одноместный `cbrt`
/// двухместным, программа получает **правдоподобный** ответ: `SysV` x86-64 кладёт
/// лишний аргумент во второй регистр SSE, а `cbrt` его не читает.
///
/// Свидетель утверждает ровно это и ни слова сверх: ответ равен кубическому
/// корню **первого** аргумента, второй не наблюдаем никак, отказа нет. То, что
/// такой вызов вообще идёт, есть свойство ABI платформы, а не обещание языка, -
/// и цена, которую уровень 1 FFI платит за отсутствие заголовков.
#[test]
fn an_over_declared_arity_is_diagnosed_by_nothing() {
    let signature = postulated("cbrt", &[PrimTy::Float64, PrimTy::Float64], PrimTy::Float64);
    let it = Foreign::new(
        LIBM,
        "cbrt",
        &[PrimTy::Float64, PrimTy::Float64],
        PrimTy::Float64,
    );
    let answer = ran(
        &signature,
        "cbrt",
        it,
        &Term::constant("cbrt").apply([literal(27.0), literal(99.0)]),
    )
    .expect("неверная арность отказом не становится: её нечем заметить");
    assert_eq!(
        bits(&answer),
        bits(&cube_root(27.0)),
        "лишний аргумент оказался наблюдаем: разбор ABI здесь другой"
    );
}

/// Разрешение символа идёт через таблицу и повторяется дёшево.
///
/// Свидетель не о скорости - о том, что второе разрешение отвечает **то же
/// самое**. Таблица, промахивающаяся по ключу, грузила бы библиотеку заново, и
/// незамеченным это осталось бы до первого `dlclose`, которого у нас нет.
#[test]
fn resolving_twice_answers_the_same() {
    let it = Foreign::new(LIBM, "cbrt", &[PrimTy::Float64], PrimTy::Float64);
    it.resolve(&Linkage::default())
        .expect("первое разрешение обязано проходить");
    it.resolve(&Linkage::default())
        .expect("второе разрешение обязано проходить");
    let first = it
        .call(&Linkage::default(), &[27.0_f64.to_bits()])
        .expect("первый вызов");
    let second = it
        .call(&Linkage::default(), &[27.0_f64.to_bits()])
        .expect("второй вызов");
    assert_eq!(first, second, "второй вызов ответил не то же, что первый");
}
