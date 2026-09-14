//! Договор третьего вычислителя: понижение отвечает то же, что `adamas eval`.
//!
//! Жанр не новый. Машину с ядром связывает
//! `the_machine_agrees_with_the_core_on_the_pure_fragment`, специализацию с
//! исполнением - `crates/adamas-interp/tests/monomorphisation.rs`; здесь третий
//! вычислитель входит в тот же договор. Свидетель - **интерпретатор**, а не
//! записанное руками ожидание: сверка своего вывода со своим же ожиданием не
//! показывает ничего.
//!
//! Проверяется не «C порождён», а прогон: текст компилируется настоящим
//! компилятором, линкуется с настоящим рантаймом и запускается.
//!
//! # Что берётся и что нет
//!
//! [`TAKEN`] - программы, которые срез обязан взять целиком. Остальным корпус
//! отвечает по факту: понижение либо отвергает их названной причиной, либо
//! берёт - и тогда ответ обязан сойтись наравне с прочими. Молчаливого
//! расхождения не бывает ни у кого.
//!
//! # Течь
//!
//! Каждый взятый прогон обязан оставить **ноль** живых блоков: RC вставляет
//! [`adamas_codegen::perceus`], и невставленный он был бы виден здесь числом.
//! Про переиспользование этот тест не говорит ничего - ноль живых блоков даётся
//! и без него; свидетель reuse стоит в `perceus.rs`.

mod harness;

use std::path::PathBuf;

/// Программы корпуса, которые срез берёт.
///
/// Чистый фрагмент: семейства и конструкторы, функции и применение, разбор,
/// рекурсия, `let`, массивы (§4.11), записи (§4.2), очистка ресурса на
/// нормальном выходе (§3.3). Плюс эффекты, гасимые **без снятия сегмента**
/// (трек B волны 4): хендлер, чьи ветки все до одной зовут резумпцию в хвосте.
/// Плюс абортивная ветка со снятием сегмента и очисткой ресурса на
/// исключительном выходе (трек C волны 4, §3.3, §3.4).
/// Плюс **одношот общего вида и параметризованный хендлер** (трек D волны 4):
/// тела второй формы дроблены кадрами по точкам приостановки, резумпция общей
/// ветки есть значение, и её судьбу решает владение.
/// Плюс **маска** (§3.4): вычисление под ней идёт под вектором без ближайшей
/// записи своей метки, и capstone `interpreter` этим берётся целиком.
/// Плюс **мультишот** (трек E волны 4): возобновление ставит копию сегмента,
/// пока на ручку резумпции есть лишние ссылки, и планировщик файберов
/// `fibers`, написанный на самом языке, этим берётся целиком.
/// Плюс **плоское значение через границу куска** (§10 вопрос 164): арифметика
/// после операции едет из куска в кусок словом, и ширина её наблюдаема.
/// Плюс **сравнения** (§4.3, трек A волны 5): аргументы плоские, ответ -
/// конструктор `Bool`, и знаковость с `totalOrder` считает `flat.c` тем же
/// ключом, каким их считает свёртка ядра.
/// Всё, что здесь стоит, обязано собраться и ответить как `adamas eval`; список
/// сокращать нельзя, а пополнять - можно и нужно, когда фрагмент растёт.
const TAKEN: [&str; 72] = [
    "abortive-cleanup",
    "abortive-except",
    "alias-computation",
    "arithmetic",
    "array-aggregate",
    "array-flat",
    "array-generic",
    "array-length-word",
    "array-nested",
    "array-tagged",
    "beta-redex",
    "case-family",
    "case-over-a-computation",
    "class-multiplicity",
    "classes",
    "comparisons",
    "decidable",
    "effect-multiplicity",
    "effects",
    "erasure",
    "execution-positions",
    "existential",
    "fibers",
    "field-effect",
    "flat",
    "flat-across-a-suspension",
    "flat-fields",
    "flat-primitives",
    "flat-under-a-parameter",
    "functor",
    "general-frames",
    "general-order",
    "instance-context-effect",
    "interpreter",
    "label-argument",
    "label-names-its-binder",
    "lists",
    "literal-default",
    "mask",
    "module-effect",
    "module-family",
    "module-resource",
    "module-scope",
    "multi-over-oneshot",
    "mutual-family",
    "mutual-polymorphic-recursion",
    "nested-case-on-a-field",
    "nested-functor",
    "nested-rowed-signature",
    "operation-higher-order",
    "operators",
    "polymorphic-recursion",
    "primitives",
    "records",
    "region-allocates-and-reads",
    "region-bound-in-the-argument",
    "region-holds-flat-payload",
    "region-strategies",
    "resource",
    "resource-cleanup",
    "rose",
    "rows",
    "sequences",
    "shadowed-name",
    "signature-effect",
    "signature-effect-parameterized",
    "soa-record",
    "state",
    "state-resource",
    "truncation",
    "unwind-inner-handler",
    "unwind-live-outer",
];

/// Замыкание над **несколькими** связываниями и порядок его среды.
///
/// Написано здесь, а не в корпусе, потому что показывает не форму языка, а
/// границу понижения: замыкание раскладывает захваченное по слотам, и порядок
/// слотов - его собственное решение. Корпус эту границу не покрывает ни одной
/// фикстурой - измерено мутантом: перестановка слотов проходила корпус целиком.
///
/// Ответ различает порядок по построению: `[3, 1, 0]` против `[1, 3, 0]`.
/// Сложение вместо списка не годилось бы - оно коммутативно, и перестановка на
/// нём ненаблюдаема.
const CAPTURES: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

runWith : (Nat -> List Nat) -> Nat -> List Nat
runWith f x = f x

main : List Nat
main =
  let first : Nat = Succ (Succ (Succ Zero))
  let second : Nat = Succ Zero
  runWith (\\n -> Cons first (Cons second (Cons n Nil))) Zero
";

/// Ответ **глубже среза**: обе печати обязаны оборваться одинаково.
///
/// Без этого свидетеля договор «то же, что интерпретатор» держался бы не
/// правилом, а тем, что ответы корпуса мельче двухсот уровней.
///
/// `times 16 16` даёт двести пятьдесят шесть `Succ` - глубину, на которой срез
/// заведомо срабатывает. Числом, а не двумя сотнями `Succ` в исходнике: писать
/// их руками значило бы вписать в тест ту самую глубину, которую он проверяет.
///
/// Совпадение здесь нетривиально, потому что глубину эти двое считают
/// по-разному: там терм со спайном применений, здесь значение со слотами.
/// Разойдись развёртка спайна на единицу - оборвётся на разном уровне.
const TOWER: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)

times : Nat -> Nat -> Nat
times Zero m = Zero
times (Succ k) m = plus m (times k m)

main : Nat
main = times 16 16
";

/// Корпус целиком: либо отказ с названной причиной, либо сошедшийся ответ.
///
/// Обе половины обязательны. Без первой список [`TAKEN`] молча усох бы; без
/// второй «не берётся» покрывало бы и тихое расхождение тоже.
///
/// Тест один на оба утверждения намеренно: два теста собирали бы одни и те же
/// фикстуры в одни и те же файлы параллельно и мешали друг другу.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
#[test]
fn the_corpus_agrees_with_the_interpreter() {
    let mut fixtures: Vec<PathBuf> = std::fs::read_dir(harness::corpus())
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    fixtures.sort();
    assert!(!fixtures.is_empty(), "корпус пуст");

    let mut taken = Vec::new();
    let mut refused = Vec::new();
    for path in &fixtures {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let source = std::fs::read_to_string(path).unwrap();
        match harness::agreed(&name, &source) {
            Ok(stderr) => {
                leakless(&name, &stderr);
                taken.push(name);
            }
            Err(error) => refused.push((name, error.to_string())),
        }
    }

    for name in TAKEN {
        assert!(
            taken.iter().any(|it| it == name),
            "{name} больше не берётся: {}",
            refused
                .iter()
                .find(|(it, _)| it == name)
                .map_or_else(|| "фикстуры нет вовсе".to_owned(), |(_, why)| why.clone())
        );
    }

    // Мера корпуса печатается прогоном, а не переписывается руками: за волну 4
    // её правили дважды, и оба раза правил прогон. Видно её под `--nocapture`.
    eprintln!(
        "корпус: взято {} из {}, отвергнуто {}",
        taken.len(),
        fixtures.len(),
        refused.len()
    );
    for (name, why) in &refused {
        eprintln!("  отвергнуто {name}: {why}");
    }

    // Границы, которых корпус не покрывает, стоят рядом со своим утверждением.
    let captures = harness::agreed("captures", CAPTURES).unwrap_or_else(|error| {
        panic!("захваты: {error}");
    });
    leakless("captures", &captures);

    // Свидетель среза сперва обязан оказаться глубже среза: без этой проверки
    // он молча выродился бы в ещё одну мелкую программу, а тест остался бы
    // зелёным и пустым.
    assert!(
        harness::printed(TOWER).contains('…'),
        "свидетель мельче среза: обрыва в ответе нет, и сверять нечего"
    );
    let tower = harness::agreed("tower", TOWER).unwrap_or_else(|error| panic!("глубина: {error}"));
    leakless("tower", &tower);
}

/// Прогон не оставил ни одного живого блока.
fn leakless(name: &str, stderr: &str) {
    let (_, live) = harness::blocks(name, stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
}

/// Наименьший размер demo target'а Фазы 6 (§9): пятьсот строк.
const DEMO_LINES: usize = 500;

/// Milestone Фазы 6 арифметичен, и арифметика его проверяется прогоном.
///
/// «500-строчная программа компилируется в native» (§9, Demo targets) держится
/// на двух фактах: программа такого размера есть, и [`TAKEN`] её берёт. Второе
/// проверяет тест выше, первое - никто, и до 2026-09-12 самая большая взятая
/// была на 473 строки. Утверждение, ничем не меряемое, тихо перестаёт быть
/// правдой при первой же чистке фикстуры, поэтому размер стоит здесь числом.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отсутствие capstone'а означает сломанный корпус"
)]
#[test]
fn the_demo_target_is_five_hundred_lines_long() {
    let path = harness::corpus().join("interpreter.adamas");
    let lines = std::fs::read_to_string(&path).unwrap().lines().count();
    assert!(
        lines >= DEMO_LINES,
        "capstone усох до {lines} строк при {DEMO_LINES} по §9"
    );
    assert!(
        TAKEN.contains(&"interpreter"),
        "capstone выпал из TAKEN: размер без понижения milestone не закрывает"
    );
}
