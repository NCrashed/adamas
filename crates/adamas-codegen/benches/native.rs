//! Первый бенчмарк понижения: во что обходится порождённая программа.
//!
//! У понижения замеров не было вовсе (§13, итог 2026-09-11: «native
//! performance не мерил никто»), и §6 оставался непроверенным целиком. Здесь
//! меряется одна его строка — **«символьно-тяжёлый код: паритет с Rust или
//! лучше»**. Взята она потому, что достижима сегодняшним срезом: §6 сам
//! называет символьный workload «цепочками функциональных преобразований над
//! деревьями и списками», а дерево, обход и свёртка — это чистый фрагмент,
//! который понижение берёт.
//!
//! Прочие строки §6 сегодня не меряются, и вот чем:
//!
//! - **Горячие циклы с unboxed numerics** и **zero-alloc циклы с регионами**
//!   требуют цикла, а цикла в языке нет: [`PrimOp`](adamas_core::prim::PrimOp)
//!   знает только `Add`, `Sub`, `Mul`, литеральный паттерн элаборация
//!   отвергает (`Missing::Literal`), и условия выхода из рекурсии по примитиву
//!   не из чего собрать. Счётчик цикла поэтому обязан быть индуктивным, то
//!   есть боксированным, и «unboxed hot loop» не выражается. Мерить нечего до
//!   сравнений и литеральных паттернов.
//! - **`@noalloc`, SIMD, mempool, FFI** — механизмов в понижении нет.
//! - **Плоские контейнеры** есть (§4.11), но хеш-таблицы, против которых
//!   меряется строка, — библиотека, которой нет.
//! - **Бизнес-код с эффектами (1.5–2x Rust)** — мерится здесь же
//!   ([`Shape::TailResumptive`], [`Shape::FlatHandled`]), но не против Rust:
//!   сосед на Rust есть только у чистой формы, а под хендлером сравниваются
//!   между собой формы понижения. Цифра 1.5–2x требует эффектного соседа,
//!   которого писать не на чем.
//! - **Старт компилятора** мерен у драйвера (`adamas-cli/benches/startup.rs`).
//! - **Время release-сборки** §6 сознательно не ограничивает; она всё равно
//!   мерена ниже как `codegen/cc`, потому что без неё не прочитать, чего стоит
//!   весь путь.
//!
//! # Алгоритм и почему он
//!
//! Двоичное дерево глубины `d`: `grow` строит, `scaled` умножает каждый лист,
//! `total` складывает. Три прохода по 2^d листьям, рекурсия глубиной `d` —
//! стека не хватить не может ни у порождённого C, ни у соседа. Листья
//! **различны** (счётчик по битам пути), поэтому перепутанные поддеревья
//! меняют ответ, а не оставляют его тем же.
//!
//! Счётчик глубины — индуктивный `Nat` длиной `d` (единицы), и его цена в
//! замере не участвует: работа экспоненциальна по `d`, а счётчик линеен.
//!
//! # Кто с кем сравнивается
//!
//! Все считают **одно и то же число**, и это проверяется до всякого
//! замера ([`checked`], [`same_answer`]):
//!
//! - `interp` — машина, то есть `adamas eval`;
//! - `native` — порождённый C, собранный `-O2` и запущенный процессом;
//! - `rust` — тот же алгоритм на Rust, теми же формами данных
//!   (`Box`-рекурсия), в этом же процессе;
//! - `floor` — тот же путь при `d = 0`: цена `fork`/`exec` и печати, которую
//!   `native` платит сверх работы.
//!
//! Сосед на Rust написан **эквивалентным кодом**, как того и требует §6
//! («Rustc на эквивалентном коде»), а не идиоматичным: те же конструкторы, та
//! же владеющая рекурсия, то же заворачивание арифметики. Идиоматичный сосед
//! (массив, цикл) мерил бы отсутствие цикла в языке, а не качество понижения.
//!
//! ## Сосед на Rust двумодален, и читать его одним числом нельзя
//!
//! Измерено семью прогонами 2026-09-12. `rust/18` ложится в две моды —
//! **21–24 мс** и **57–64 мс**, — и мода видна уже на `rust/16` (≤ 5.2 мс
//! против ≥ 5.3 мс), то есть устанавливается до замера. Внутри прогона
//! интервал узок в обеих модах; между прогонами разброс двух-с-половиной
//! кратный. Точки `native/*` при этом стабильны: `pure/18` даёт 43–46 мс во
//! **всех** прогонах, `floor` — 0.45 мс.
//!
//! Значит разброс принадлежит соседу, а не стенду и не машине; §13 за
//! 2026-09-11 подозревал аллокаторный шум у `rust/16` — на `rust/18` он
//! оказался решающим. Практическое следствие: **сравнение `pure` с `rust`
//! одним прогоном не воспроизводится**, и вывод «понижение обгоняет Rust в
//! полтора раза на глубине 18» прочитан с медленной моды. Устойчивое
//! сравнение здесь одно — `handled` против `boxed`: обе точки стабильны, обе
//! идут одним и тем же путём.
//!
//! # Чем проверено, что мерится не пустота
//!
//! Тремя вещами разом. Ответ **печатается** и сверен с машиной — выброси
//! компилятор C вычисление, печатать станет нечего. Точек по глубине три, и
//! шаг глубины удваивает работу: линейному исполнению отвечает удвоение
//! времени. И `floor` показывает, сколько в измеренном не работа, а запуск
//! процесса.
//!
//! Точка `native/handled` сверх того проверена двумя мутантами, и оба
//! пойманы.
//!
//! - **Работа.** `scaled (Node l r) = Node l r` — свёртка перестаёт спускаться
//!   по дереву. Ответ меняется (309237252096 → 103079084032, ровно треть),
//!   время на глубине 16 падает 18.8 → 9.9 мс, блоки 1835025 → 524308.
//!   Заодно пойман соседом на Rust: `assert_eq!` у `rust/*` сработал раньше
//!   всех прочих.
//! - **Операция.** `scale ask x` → `scale Triple x` при сохранённых row,
//!   объявлении эффекта и хендлере. Ответ тот же, а разность точек **исчезает
//!   целиком**: `handled` садится на `boxed` и по времени (4.03 против 4.06 мс
//!   на глубине 14), и по блокам (49168 против 49165). Значит измеряемая
//!   разность есть операция, а не вторая форма вообще.
//!
//! Второй мутант заодно показал, чего в решении 3 волны 4 не написано:
//! кадр ставится **не** на всякий вызов второй формы, а только там, откуда
//! приостановка достижима. У мутанта `scaled` осталась второй формой — берёт
//! `ev` и `kont`, — но `adamas_kont_push` в порождённом C не встречается ни
//! разу, и рекурсия идёт прямыми вызовами.
//!
//! Точка `native/handled-flat` держится на том же ответе и сверх того на двух
//! свидетелях вне стенда: `tests/boundary.rs` смотрит **представление** в
//! тексте C, а корпусная `eval/flat-across-a-suspension` — ширину перевода
//! через `Float64`. Стенд один их не заменяет: у него множитель целый, а на
//! целых подмена ширины сокращается — C приводит число обратно.
//!
//! # Цена хендлера: против чего она мерится
//!
//! Формы четыре, и ни одна не заведена для симметрии. Мерить `handled` против
//! `pure` было бы враньём: между ними **два** различия, а не одно.
//!
//! Различие первое — операция. Различие второе — представление множителя.
//! Отсюда [`Shape::Boxed`]: тот же алгоритм, множитель — **нульарный
//! конструктор** `Mult`, который применяет к листу чистая `scale`. Конструктор
//! без рантайм-полей объектом не становится (ABI 2026-09-08), то есть ячейки
//! кучи боксирование здесь не стоит; стоит оно вызова `scale` на лист, и
//! платят его `Boxed` и `TailResumptive` **одинаково**. Разность этих двух
//! точек — цена второй формы понижения на этом алгоритме: вектор evidence
//! скрытым аргументом, дробление тела `scaled` кадрами по точкам
//! приостановки и диспетчер операции. Она и есть число milestone 3, от
//! которого вопрос 74 считает выигрыш инлайнинга.
//!
//! Точка `pure` при этом не сдвинулась ни на строку исходника: строка §6
//! «символьно-тяжёлый код» мерится ею и сравнивается с соседом на Rust, а
//! путь под хендлер лежит рядом, а не поверх.
//!
//! ## Четвёртая точка: эффект над плоскими данными
//!
//! [`Shape::FlatHandled`] — умножение стоит **после** операции
//! (`Leaf (mulInt64 x (factor ask))`), то есть плоское значение переживает
//! точку приостановки и пересекает границу куска дроблёного тела. До
//! 2026-09-12 такая программа не мерилась вовсе: понижение отвечало на неё
//! `Ok`, а печатало C, который не собирается (§10 вопрос 164). Стенд обходил
//! это, унося арифметику внутрь `scale`; обход снят, и точка мерится.
//!
//! Мерится она против `pure`, а не против `handled`: это и есть «цена эффекта
//! над плоскими данными» — то, ради чего §4.11 писался. Различий с `pure` три,
//! и все три названы разностью блоков ниже.
//!
//! Множителей два (`Triple` и `Double`), хотя программе нужен один: с одним
//! конструктором ветка `ask -> resume Triple` не имела бы мутанта — вернуть
//! из хендлера **не то** было бы не из чего.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{PRINT_DEPTH, Term};
use adamas_elab::class::Instances;
use adamas_elab::fixity::Fixities;
use adamas_elab::mono;
use adamas_elab::{Owned, Warnings};
use criterion::{Criterion, criterion_group, criterion_main};

/// Глубины дерева: шаг удваивает работу, и все четверо считаются на одних и
/// тех же трёх точках.
const DEPTHS: [usize; 3] = [14, 16, 18];

/// Глубина, на которой мерится цена самого понижения.
const CODEGEN_DEPTH: usize = 16;

// --- исходник -----------------------------------------------------------

/// Форма программы: чистый сосед, он же с указательным множителем, тот же
/// алгоритм под хендлером и он же с плоской арифметикой после операции.
///
/// Все четыре считают одно число. Различие ровно одно на каждом шаге: `Pure` →
/// `Boxed` меняет представление множителя, `Boxed` → `TailResumptive` меняет
/// литерал на операцию `ask`, чья ветка зовёт `resume` в хвосте,
/// `TailResumptive` → `FlatHandled` возвращает арифметику **после** операции,
/// откуда её уносил обход. Порознь, потому что вместе они мерили бы сумму.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    /// Чистый сосед: множитель написан литералом.
    Pure,
    /// Множитель — указательное значение, хендлера нет.
    Boxed,
    /// Тот же алгоритм под хвостово резумптивным хендлером.
    TailResumptive,
    /// Он же, но умножение стоит после операции: плоское значение пересекает
    /// границу куска дроблёного тела.
    FlatHandled,
}

impl Shape {
    /// Имя в идентификаторе точки замера.
    const fn name(self) -> &'static str {
        match self {
            Self::Pure => "pure",
            Self::Boxed => "boxed",
            Self::TailResumptive => "handled",
            Self::FlatHandled => "handled-flat",
        }
    }
}

/// Указательный множитель: тип и функция, применяющая его к листу.
///
/// Делится `Boxed` и `TailResumptive` дословно — иначе разность точек мерила
/// бы не операцию.
///
/// Арифметика уехала **внутрь** `scale` намеренно: у `handled` операция дробит
/// тело `scaled`, и разность `handled − boxed` обязана быть операцией и ничем
/// сверх. Плоское значение после операции границу куска пересекает
/// (§10 вопрос 164), и мерится оно отдельной точкой — [`Shape::FlatHandled`].
const MULTIPLIER: &str = "\
data Mult where
  Triple : Mult
  Double : Mult

scale : Mult -> Int64 -> Tree
scale Triple x = Leaf (mulInt64 x 3)
scale Double x = Leaf (mulInt64 x 2)
";

/// Множитель числом: его берёт форма с арифметикой после операции.
const FACTOR: &str = "\
factor : Mult -> Int64
factor Triple = 3
factor Double = 2
";

/// Программа: дерево глубины `depth`, построенное, умноженное и свёрнутое.
fn source(shape: Shape, depth: usize) -> String {
    let mut nat = String::new();
    for _ in 0..depth {
        nat.push_str("(Succ ");
    }
    nat.push_str("Zero");
    for _ in 0..depth {
        nat.push(')');
    }

    // Разница форм — объявления, row у `scaled` и то, откуда берётся
    // множитель. Остальное общее дословно.
    let (declarations, row, leaf) = match shape {
        Shape::Pure => (String::new(), "", "Leaf (mulInt64 x 3)"),
        Shape::Boxed => (MULTIPLIER.to_owned(), "", "scale Triple x"),
        // `Unit` объявлением эффекта требуется: нульарная операция пишется
        // через него.
        Shape::TailResumptive => (
            format!(
                "{MULTIPLIER}\n\
                 data Unit where\n  MkUnit : Unit\n\n\
                 effect Ask where\n  ask : Mult\n"
            ),
            "{Ask} ",
            "scale ask x",
        ),
        Shape::FlatHandled => (
            format!(
                "{MULTIPLIER}\n{FACTOR}\n\
                 data Unit where\n  MkUnit : Unit\n\n\
                 effect Ask where\n  ask : Mult\n"
            ),
            "{Ask} ",
            "Leaf (mulInt64 x (factor ask))",
        ),
    };
    // Хвост программы. У `pure` он тот же, каким мерена строка §6, и трогать
    // его нельзя. У прочих двух свёртка вынесена за `handle`: приостановленное
    // вычисление, как и ответ ветки, обязано быть указательным (§4.11), а
    // `Int64` плоский. Вынесена **у обоих**, чтобы разность точек оставалась
    // операцией и ничем сверх.
    //
    // `computed` названо связыванием верхнего уровня, а не написано в
    // `handle`: приостановленное вычисление хендлер берёт с написанным типом
    // (§3.4).
    let tail = match shape {
        Shape::Pure => {
            "computed : Int64\n\
             computed = total (scaled (grow depth 1))\n\
             \n\
             main : Int64\n\
             main = computed\n"
        }
        Shape::Boxed => {
            "computed : Tree\n\
             computed = scaled (grow depth 1)\n\
             \n\
             main : Int64\n\
             main = total computed\n"
        }
        Shape::TailResumptive | Shape::FlatHandled => {
            "computed : {Ask} Tree\n\
             computed = scaled (grow depth 1)\n\
             \n\
             answered : Tree\n\
             answered = handle computed with\n\
             \x20 return v -> v\n\
             \x20 ask -> resume Triple\n\
             \n\
             main : Int64\n\
             main = total answered\n"
        }
    };

    format!(
        "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Tree where
  Leaf : Int64 -> Tree
  Node : Tree -> Tree -> Tree

{declarations}
-- Лист получает номер пути в двоичной записи: значения различны, и
-- переставленные поддеревья меняют ответ.
grow : Nat -> Int64 -> Tree
grow Zero seed = Leaf seed
grow (Succ k) seed =
  let doubled : Int64 = mulInt64 seed 2
  Node (grow k doubled) (grow k (addInt64 doubled 1))

scaled : Tree -> {row}Tree
scaled (Leaf x) = {leaf}
scaled (Node l r) = Node (scaled l) (scaled r)

total : Tree -> Int64
total (Leaf x) = x
total (Node l r) = addInt64 (total l) (total r)

depth : Nat
depth = {nat}

{tail}"
    )
}

// --- машина -------------------------------------------------------------

/// Элаборированная программа вместе с тем, что о ней знает разрешение.
fn elaborated(source: &str) -> (Signature, Metas, Instances) {
    let module = adamas_parser::parse(source).expect("исходник обязан разбираться");
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut fixities = Fixities::default();
    let mut instances = Instances::default();
    let mut warnings = Warnings::new();
    adamas_elab::elaborate_into(
        &module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut fixities,
        &mut instances,
        &mut warnings,
    )
    .expect("исходник обязан проходить проверку");
    (signature, metas, instances)
}

/// Тело `main` с подставленными аргументами уровня и row — то, что вычисляет
/// `adamas eval`.
fn entry(signature: &Signature) -> Term {
    let definition = signature.lookup("main").expect("`main` объявлен");
    let body = definition.body.as_ref().expect("у `main` есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    body.substitute_levels(&levels).substitute_rows(&rows)
}

/// Программа, готовая к замеру обоими путями.
struct Program {
    signature: Signature,
    /// Терм, как написан: его считает машина.
    written: Term,
    /// Он же после специализации: его понижает бэкенд.
    made: Term,
    /// Ответ по мнению машины.
    answer: String,
}

impl Program {
    fn new(shape: Shape, depth: usize) -> Self {
        let text = source(shape, depth);
        let (mut signature, mut metas, instances) = elaborated(&text);
        let written = entry(&signature);
        let answer = adamas_interp::run(&signature, &written)
            .expect("операция обязана встретить хендлер")
            .printed(Some(PRINT_DEPTH))
            .to_string();
        let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
            .expect("специализация обязана пройти")
            .term;
        Self {
            signature,
            written,
            made,
            answer,
        }
    }

    /// Текст C либо названный отказ понижения.
    fn lowered(&self) -> Result<String, adamas_codegen::CompileError> {
        adamas_codegen::compile(&self.signature, &self.made)
    }
}

// --- порождённый C ------------------------------------------------------

/// Место под порождённый C и его сборку.
fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join("bench-native");
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Объектные файлы рантайма: собираются однажды на весь прогон.
///
/// `-O2`, а не `-O1` тестового харнесса: замер говорит о том, что получит
/// пользователь release-сборкой, и уровень оптимизации — часть окружения,
/// которое число обязано нести рядом с собой.
fn runtime() -> &'static [PathBuf] {
    static OBJECTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    OBJECTS.get_or_init(|| {
        let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
        let dir = scratch();
        [
            "object.c",
            "array.c",
            "region.c",
            "evidence.c",
            "closure.c",
            "frame.c",
        ]
        .iter()
        .map(|name| {
            let object = dir.join(format!("{name}.o"));
            let status = Command::new(env!("ADAMAS_CC"))
                .args(["-std=c11", "-O2", "-c"])
                .arg("-I")
                .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
                .arg(sources.join(name))
                .arg("-o")
                .arg(&object)
                .status();
            assert!(
                status.is_ok_and(|status| status.success()),
                "рантайм не собрался: {name}"
            );
            object
        })
        .collect()
    })
}

/// Собирает порождённый C в исполняемый файл.
fn built(name: &str, text: &str) -> PathBuf {
    let dir = scratch();
    let source = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&source, text).unwrap();
    compiled(&source, &binary);
    binary
}

/// Вызов компилятора C — отдельно, потому что он же и мерится.
fn compiled(source: &Path, binary: &Path) {
    let output = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O2", "-fwrapv", "-w"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(source)
        .args(runtime())
        .arg("-o")
        .arg(binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "порождённый C не собрался:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Прогон собранной программы: ответ на stdout, счётчики блоков на stderr.
fn ran(binary: &Path) -> (String, String) {
    let output = Command::new(binary).output().unwrap();
    assert!(
        output.status.success(),
        "прогон оборвался: {}",
        output.status
    );
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// Собранная программа, чей ответ уже сверен с машиной.
fn checked(program: &Program, name: &str) -> PathBuf {
    let text = program.lowered().expect("чистая форма обязана понижаться");
    let binary = built(name, &text);
    let (stdout, stderr) = ran(&binary);
    assert_eq!(
        stdout.trim_end_matches('\n'),
        program.answer,
        "{name}: понижение посчитало не то, что машина"
    );
    // Счётчики печатает точка входа безусловно; строку видно в отчёте прогона
    // `--test`, и по ней читается, сработал ли reuse.
    eprintln!("{name}: ответ {}, {}", program.answer, stderr.trim_end());
    binary
}

// --- сосед на Rust ------------------------------------------------------

/// Тот же алгоритм эквивалентным кодом: те же конструкторы, та же владеющая
/// рекурсия, то же заворачивание.
enum Tree {
    Leaf(i64),
    Node(Box<Tree>, Box<Tree>),
}

fn grow(depth: usize, seed: i64) -> Tree {
    if depth == 0 {
        return Tree::Leaf(seed);
    }
    let doubled = seed.wrapping_mul(2);
    Tree::Node(
        Box::new(grow(depth - 1, doubled)),
        Box::new(grow(depth - 1, doubled.wrapping_add(1))),
    )
}

fn scaled(tree: Tree) -> Tree {
    match tree {
        Tree::Leaf(x) => Tree::Leaf(x.wrapping_mul(3)),
        Tree::Node(left, right) => Tree::Node(Box::new(scaled(*left)), Box::new(scaled(*right))),
    }
}

fn total(tree: Tree) -> i64 {
    match tree {
        Tree::Leaf(x) => x,
        Tree::Node(left, right) => total(*left).wrapping_add(total(*right)),
    }
}

fn neighbour(depth: usize) -> i64 {
    total(scaled(grow(depth, 1)))
}

// --- замеры -------------------------------------------------------------

fn symbolic(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("symbolic");
    // Точка `native` — запуск процесса, точка `interp` — секунды: сотня
    // выборок по умолчанию превратила бы прогон в часы.
    group.sample_size(10);

    // Цена запуска процесса и печати: та же программа без работы.
    let floor = Program::new(Shape::Pure, 0);
    let binary = checked(&floor, "floor");
    group.bench_function("floor", |bencher| bencher.iter(|| ran(&binary)));

    // Сосед на Rust — только у чистой формы: под хендлером сравнивать не с
    // чем, там сравниваются между собой `boxed` и `handled`.
    for depth in DEPTHS {
        let pure = Program::new(Shape::Pure, depth);
        let expected: i64 = pure.answer.parse().expect("ответ — число");
        assert_eq!(
            neighbour(depth),
            expected,
            "сосед на Rust считает не тот же алгоритм"
        );
        group.bench_function(format!("rust/{depth}"), |bencher| {
            bencher.iter(|| neighbour(depth));
        });
    }

    same_answer();

    for shape in [
        Shape::Pure,
        Shape::Boxed,
        Shape::TailResumptive,
        Shape::FlatHandled,
    ] {
        let name = shape.name();
        for depth in DEPTHS {
            let program = Program::new(shape, depth);
            let text = program
                .lowered()
                .unwrap_or_else(|error| panic!("{name}/{depth}: понижение отвергает: {error}"));
            let binary = built(&format!("{name}{depth}"), &text);
            let (stdout, stderr) = ran(&binary);
            assert_eq!(
                stdout.trim_end_matches('\n'),
                program.answer,
                "{name}/{depth}: понижение посчитало не то, что машина"
            );
            eprintln!(
                "native/{name}/{depth}: ответ {}, {}",
                program.answer,
                stderr.trim_end()
            );
            group.bench_function(format!("native/{name}/{depth}"), |bencher| {
                bencher.iter(|| ran(&binary));
            });
        }
        for depth in DEPTHS {
            let program = Program::new(shape, depth);
            group.bench_function(format!("interp/{name}/{depth}"), |bencher| {
                bencher.iter(|| adamas_interp::run(&program.signature, &program.written).unwrap());
            });
        }
    }

    group.finish();
}

/// Четыре формы обязаны считать одно число.
///
/// Иначе «тот же алгоритм под хендлером» было бы неправдой, и разность точек
/// мерила бы разные программы. Проверяется на мелкой глубине: свойство это
/// формы, а не размера.
fn same_answer() {
    let sample = DEPTHS[0];
    let pure = Program::new(Shape::Pure, sample).answer;
    for shape in [Shape::Boxed, Shape::TailResumptive, Shape::FlatHandled] {
        assert_eq!(
            pure,
            Program::new(shape, sample).answer,
            "форма `{}` считает не то же число",
            shape.name()
        );
    }
}

fn codegen(criterion: &mut Criterion) {
    let program = Program::new(Shape::Pure, CODEGEN_DEPTH);
    let lowered = adamas_codegen::lower::lower(&program.signature, &program.made)
        .expect("чистая форма обязана понижаться");
    let inserted = adamas_codegen::perceus::insert(lowered.clone());
    let text = adamas_codegen::emit_c::emit(&inserted).expect("форма понижения известна эмиттеру");

    let mut group = criterion.benchmark_group("codegen");
    group.bench_function("lower", |bencher| {
        bencher.iter(|| adamas_codegen::lower::lower(&program.signature, &program.made).unwrap());
    });
    group.bench_function("perceus", |bencher| {
        bencher.iter(|| adamas_codegen::perceus::insert(lowered.clone()));
    });
    group.bench_function("emit", |bencher| {
        bencher.iter(|| adamas_codegen::emit_c::emit(&inserted).unwrap());
    });

    // §6 время сборки не ограничивает — точка стоит затем, чтобы доля
    // понижения в общем пути читалась, а не угадывалась.
    let dir = scratch();
    let source = dir.join("codegen.c");
    let binary = dir.join("codegen");
    std::fs::write(&source, &text).unwrap();
    group.sample_size(10);
    group.bench_function("cc", |bencher| bencher.iter(|| compiled(&source, &binary)));
    group.finish();
}

criterion_group!(benches, symbolic, codegen);
criterion_main!(benches);
