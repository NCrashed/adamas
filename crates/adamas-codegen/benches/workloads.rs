//! Нагрузки трека Z, кроме символьной: скалярный цикл, FBIP-цикл, колонное ядро.
//!
//! Трек Z Фазы 7 (`docs/phase7-plan.md`) мерит разрыв двух бэкендов на четырёх
//! нагрузках — скалярная арифметика, аллокационно-тяжёлый символьный код,
//! FBIP-цикл, SIMD-ядро. LLVM-эмиттера ещё нет, поэтому здесь берётся первая
//! половина обязательства: те же нагрузки на **одном** бэкенде, чтобы к приходу
//! второго было с чем сравнивать. Таблица — `docs/measurements/workload-gap/`.
//!
//! Символьная нагрузка мерится не здесь, а в `native.rs`: там же живёт и
//! **методика**, которой подчиняется этот стенд. Читать её надо там; здесь
//! три нагрузки и их соседи.
//!
//! # Программы живут в корпусе, а не здесь
//!
//! Ни одна из трёх нагрузок в этом файле не написана. Пункт 1 милестоуна волны
//! 5 требует, чтобы нагрузка была **программой в корпусе**, взятой понижением и
//! сверенной с машиной; корпусную программу прогоняет `tests/agreement.rs`
//! договором трёх вычислителей, стендовую не прогоняет никто. Размер при этом
//! обязан различаться — машине полсотни миллионов витков не по силам, — и
//! ровно здесь заводился бы разъезд: две копии одной программы, из которых
//! проверяется одна, а мерится другая.
//!
//! Копия поэтому **одна**: стенд читает корпусный файл и переписывает в нём
//! только строки размера ([`harness::resized`]), а имя размера, встретившееся
//! не ровно один раз, роняет стенд. Сверка с машиной идёт по файлу **как он
//! есть**, без подстановки.
//!
//! Второй записи не избежать ровно в одном месте — у **соседа на Rust**: §6
//! требует эквивалентного кода, то есть отдельной реализации. Разъезд с ней
//! ловится ответом: обе стороны печатают число, и стенд сверяет их на полном
//! размере.
//!
//! # Почему отдельный стенд, а не ещё две группы в `native.rs`
//!
//! Требование Z дословно: «каждая строка воспроизводится одной командой».
//! Фильтр criterion гасит **точки**, но не подготовку вокруг них: парный замер
//! `native.rs` идёт после `group.finish()` и стоит минут. Команда, обязанная
//! воспроизвести одну строку, тянула бы за собой весь символьный стенд.
//! Общее у двух стендов вынесено в `harness`, а не скопировано.
//!
//! # Первая нагрузка: скалярная арифметика, и почему у неё две формы
//!
//! `mix n acc = mix (n − 1) (f acc n)`, счётчик и накопитель плоские. Форм
//! цепочки две ([`Chain`]), и вторая заведена **замером**, а не для полноты.
//!
//! Естественная запись — `acc · K + n` с множителем-литералом. Она даёт разрыв
//! с соседом **в восемь раз**, и ни одна его доля нам не принадлежит:
//! развёрнутая на `U` витков, аффинная цепочка с постоянным `K` складывается
//! обратно в одно умножение на `K^U` плюс член, линейный по счётчику. LLVM это
//! делает, gcc нет. Проверено тремя способами, и все три говорят одно: тот же
//! цикл руками на C стоит столько же, сколько наш; тот же цикл на Rust с
//! множителем **из аргумента** стоит столько же, сколько наш; а цепочка
//! `acc · acc · K + n`, которую разворачивать нечем, ставит отношение на
//! **паритет**. Первые два свидетеля — `scalar-decomposition.sh`, третий —
//! точка [`Chain::Squaring`] рядом. Числа — в таблице, здесь их второй копии
//! нет намеренно.
//!
//! Мерятся поэтому обе, и в таблице стоят обе. Выкинуть аффинную значило бы
//! спрятать восьмикратный разрыв, который существует; выкинуть нелинейную —
//! выдать одну оптимизацию LLVM за качество понижения.
//!
//! До трека A волны 5 нагрузка не выражалась ни в одной форме: счётчик обязан
//! был быть индуктивным. Теперь он плоский, и это наблюдаемо — прогон печатает
//! **ноль** выданных блоков, то есть на витке нет ни ячейки кучи (проверяется
//! ниже, а не предполагается).
//!
//! Самовызов в хвосте в порождённом C записан обычным вызовом `fn_1(...)`,
//! петли эмиттер не строит. Что она всё-таки получается, проверено прогоном, а
//! не чтением: [`SCALAR_TURNS`] витков — это глубина рекурсии, на которой
//! кадров не хватило бы никакому стеку, и прогон её проходит. Сосед той же
//! проверки не проходит и потому написан петлёй — см. «сосед на Rust» ниже.
//!
//! # Третья нагрузка: FBIP-цикл
//!
//! Список из [`FBIP_CELLS`] ячеек, [`FBIP_PASSES`] проходов; проход
//! (`step`) разбирает `Cons` и строит `Cons` — каноническая форма §5.1, в
//! которой Perceus переписывает разобранную ячейку вместо того, чтобы ронять
//! её и брать новую. Свёртка `total` умножает накопитель на три, поэтому она
//! чувствительна к порядку: проход список **разворачивает**, и потерянный
//! проход виден ответом, а не только временем.
//!
//! Наблюдаемое здесь не время, а счётчик: блоков выдано ровно
//! [`FBIP_CELLS`] — столько, сколько построил `build`. Все
//! [`FBIP_PASSES`] проходов стоят **ноль** ячеек. Это и проверяется
//! утверждением: строка, у которой reuse отвалился, упадёт здесь, а не
//! разойдётся на проценты во времени.
//!
//! Сосед на Rust написан **эквивалентным кодом** (§6: «Rustc на эквивалентном
//! коде»): тот же список из `Cons`/`Nil` на `Box`, то же владение, тот же
//! порядок «освободить, потом взять». Reuse у него не бывает по построению — `Box::new`
//! берёт ячейку, а разобранная уходит в `free`, — и это не поддавка, а ровно
//! то, что §5.1 обещает выиграть: «без FBIP каждое преобразование = O(n)
//! аллокаций; с FBIP на уникальных инпутах — 0».
//!
//! # Четвёртая нагрузка: скалярный эквивалент SIMD-ядра
//!
//! Самой `Simd n a` (§4.9) в языке нет — ни типа, ни класса `Primitive`, ни
//! операций, ни выравненных буферов; проверено прогоном (`adamas check` на
//! `lane : Simd 4 Float32` отвечает «имя `Simd` не найдено»), и это трек H Фазы
//! 7. Скалярная половина ядра доступна сегодня, и она здесь.
//!
//! **Форма ядра взята у §4.9, а не выбрана.** Там сказано дословно: «ширина
//! `Simd` есть число обрабатываемых сущностей, а не число компонент величины»,
//! и «внутренний цикл работает с `Simd 8 Float32` над колонкой». Значит
//! векторизуемое ядро есть element-wise проход по плоской колонке `Float32`, а
//! скалярный его эквивалент — тот же проход по одной дорожке:
//! `x[i] := x[i]·gain + bias`, [`COLUMN_PASSES`] раз по [`COLUMN_CELLS`]
//! ячейкам.
//!
//! Прежняя редакция стенда объявляла этот эквивалент «неотличимым от первой
//! нагрузки» и потому не заводила. **Довод не подтвердился, и это измерено:**
//! первая нагрузка держится паритета, колонная отстаёт от соседа в семь раз, а
//! мутант, вынимающий из ядра чтение ячейки, режет отставание втрое. Обращения
//! к ячейке у скалярной строки нет ни одного, и вынимать там нечего.
//!
//! Отвергнутые формы ядра, каждая по своей причине:
//!
//! - **скалярное произведение** — свёртка `acc := acc + x[i]·w[i]` есть
//!   зависимая цепочка плавающих сложений, и её латентность (около четырёх
//!   тактов на элемент) заслонила бы то, ради чего строка заводится;
//! - **проход по `Array n Vec3`** (центральный пример §4.11) — мерил бы
//!   доступ с шагом по агрегату, тогда как §4.9 прямо говорит, что `Vec3` не
//!   `Simd` и что в регистр грузятся координаты **разных** сущностей, а не
//!   компоненты одной.
//!
//! Свёртка ядра — **вычитанием** (`acc := x[i] - acc`), и выбрана она замером:
//! у `acc := acc·gain + x[i]` на миллионах витков ответ уходит в `inf`, а
//! `acc := acc + x[i]` не видит перестановки двух ячеек. Числа — в шапке
//! корпусной программы.
//!
//! # Что колонная строка мерит, и чем это установлено
//!
//! Не трафиком памяти — **ценой обращения**, и разошлось это с ожиданием.
//! Мутант «та же работа на колонке, помещающейся в кэш» (67 108 864 обращения
//! при 262 144 ячейках вместо 8 388 608) не ответил: за вычетом заполнения и
//! свёртки ядро идёт 165.1 мс на тридцати двух мегабайтах и 169.8 мс на одном.
//! Потолок того же цикла руками на C — 44.2 мс, то есть память здесь не узкое
//! место вовсе.
//!
//! Разложение (`docs/measurements/workload-gap/column-decomposition.sh`, те же
//! размеры и та же строка сборки) называет, где сидят остальные 170 мс:
//! проверка границы стоит 5.8, шаг рантаймом — ничего, а **счётчик ссылок на
//! заголовке колонки — 178.6**. Пара `dup`/`drop` вокруг чтения и проверка
//! уникальности перед записью идут через одно и то же поле заголовка, и
//! зависимость «запись — чтение» на нём сериализует виток и отнимает у gcc
//! векторизацию.
//!
//! # Что сверяется до всякого замера
//!
//! - **Ответ машины** — на корпусном размере, по корпусному тексту без
//!   подстановки. Полный размер машине не по силам: [`SCALAR_TURNS`] витков
//!   интерпретатор считал бы часами. Мелкий размер ловит то, ради чего сверка и
//!   стоит: расхождение семантики, а не арифметики большого числа.
//! - **Ответ соседа** — на полном. Обе стороны печатают число, и совпадение на
//!   [`SCALAR_TURNS`] витках означает, что заворачивание, порядок и знаковость
//!   у них одни.
//! - **Счётчики блоков** — у всех трёх нагрузок, утверждением.
//!
//! # Чем проверено, что строки мерят названное
//!
//! Всем трём подсунуто замедление, и все три ответили (2026-09-15).
//!
//! - **Скалярной** — лишнее умножение в цепочке, у обеих сторон разом
//!   (`acc · K + n` → `acc · acc · K + n`). Наша сторона 47.1 → 77.7 мс, и это
//!   ровно то, чего стоит второе умножение в зависимой цепочке. Заодно
//!   выяснилось главное про эту нагрузку: сосед на том же шаге идёт 7.6 → 72.5,
//!   то есть в **девять с половиной раз**, и шестикратный разрыв аффинной
//!   формы обращается в паритет. Отсюда две цепочки в таблице, а не одна.
//! - **FBIP** — выключенный reuse: одна строка [`adamas_codegen::perceus`]
//!   (`Reclaim` не заводится никогда), и всё остальное как было. Блоков стало
//!   6 500 000 вместо 100 000 — ровно ячейка на элемент на проход, — время
//!   14.1 → 36.9 мс, отношение 0.45 → **1.22**. То есть строка мерит именно
//!   переписывание на месте: без него понижение оказывается **медленнее**
//!   соседа, платя ту же аллокацию плюс счётчик ссылок.
//!
//!   Утверждение о счётчике этот мутант ловит первым и без всякого времени:
//!   прогон падает на «проход выдал ячейки».
//! - **Колонной** — вынутое из ядра чтение ячейки, у обеих сторон разом
//!   (`x[i] := x[i]·gain + bias` → `x[i] := bias·gain + bias`). Наша сторона
//!   213.2 → 83.7 мс, сосед 30.5 → 28.7, отношение 7.00 → **2.89**. То есть
//!   строка мерит именно обращение к плоской ячейке: соседу оно почти ничего не
//!   стоит, нам — две трети времени.
//!
//!   Второй мутант той же строки **не ответил**, и это результат, а не
//!   осечка: та же работа на колонке, помещающейся в кэш, идёт столько же (см.
//!   выше). Читать строку надо как «цена обращения», а не «трафик памяти».

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

mod harness;

use adamas_codegen::emit_llvm::Artefacts;
use adamas_codegen::llvm::Pipeline;
use adamas_core::term::PRINT_DEPTH;
use adamas_elab::mono;
use criterion::{Criterion, SamplingMode, criterion_group};

use harness::{
    Backend, Column, Load, NEIGHBOUR, SUPPORT_LEVEL, built, by_floor, corpus, elaborated, entry,
    llvm_against_c, ran, ran_neighbour, ratio, resized, same_work,
};

/// Место под порождённый C и его сборку — своё у стенда.
const STAND: &str = "bench-workloads";

/// Множитель скалярной цепочки: тот же, что у `PCG`-семейства.
///
/// Написан **дважды** — здесь и в корпусной программе, — и это единственное
/// место, где второй записи не избежать: сосед по §6 есть отдельная реализация
/// на Rust, а не подстановка. Разъезд ловится ответом: стенд сверяет число
/// соседа с числом понижения на **полном** размере, и множитель, разошедшийся
/// в последнем разряде, роняет прогон.
const MIX: u64 = 6_364_136_223_846_793_005;

/// Форма скалярной цепочки. Различаются они одним умножением, а числом — в
/// восемь раз, и вся разница принадлежит **соседу**, не нам.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Chain {
    /// `acc := acc · acc · K + n`. По `acc` нелинейна, разворачивать нечего.
    Squaring,
    /// `acc := acc · K + n` — аффинная, и множитель у неё **литерал**.
    ///
    /// Развёрнутая на `U` витков, такая цепочка складывается обратно: `K^U`
    /// считается на компиляции, а сумма `Σ K^j · b_j` линейна по счётчику.
    /// LLVM это делает, gcc нет, и отсюда восьмикратный разрыв, к понижению
    /// отношения не имеющий. Свидетели — `scalar-decomposition.sh` и точка
    /// [`Chain::Squaring`] рядом.
    Affine,
}

impl Chain {
    const ALL: [Self; 2] = [Self::Squaring, Self::Affine];

    /// Имя группы замера и запроса к соседу.
    const fn name(self) -> &'static str {
        match self {
            Self::Squaring => "scalar",
            Self::Affine => "scalar-affine",
        }
    }

    /// Имя корпусной фикстуры: программа живёт там, а не здесь.
    const fn fixture(self) -> &'static str {
        match self {
            Self::Squaring => "workload-scalar",
            Self::Affine => "workload-scalar-affine",
        }
    }

    /// Он же на Rust — те же операции в том же порядке.
    fn mix(self, n: u64) -> u64 {
        let (mut acc, mut left): (u64, u64) = (0, n);
        match self {
            Self::Squaring => {
                while left != 0 {
                    acc = acc.wrapping_mul(acc).wrapping_mul(MIX).wrapping_add(left);
                    left -= 1;
                }
            }
            Self::Affine => {
                while left != 0 {
                    acc = acc.wrapping_mul(MIX).wrapping_add(left);
                    left -= 1;
                }
            }
        }
        acc
    }
}

/// Витков скалярного цикла.
///
/// Выбрано так, чтобы работа была на два порядка выше пола запуска процесса
/// (~0.2 мс): полсотни миллионов витков идут около 50 мс.
const SCALAR_TURNS: u64 = 50_000_000;

/// Ячеек в списке FBIP-цикла и проходов по нему.
///
/// Ячеек столько, чтобы список не помещался в кэш и обход платил за память;
/// проходов столько, чтобы построение списка (единственное место, где ячейки
/// выдаются) было малой долей измеряемого — иначе мерился бы `build`, а не
/// reuse.
const FBIP_CELLS: i64 = 100_000;
const FBIP_PASSES: i64 = 64;

/// Длина колонки скалярного ядра и число проходов по ней.
///
/// Длина взята **больше последнего уровня кэша**: 8 388 608 ячеек по четыре
/// байта — 32 мегабайта против 24 у L3 этого хоста. Выбрана она так затем,
/// чтобы у соседа строка мерила настоящий поток в память, а не кэш: потолок
/// того же цикла руками на C идёт 44.2 мс на гигабайт трафика, то есть на
/// пропускной способности.
///
/// **Нашей стороны это не касается, и вот тут ожидание не подтвердилось.** Та
/// же работа на колонке в один мегабайт идёт столько же (169.8 против 165.1 мс
/// за вычетом заполнения и свёртки): проход упирается не в память, а в счётчик
/// ссылок на заголовке колонки. Разложение — в `column-decomposition.sh`,
/// пересказ — в шапке.
///
/// Проходов столько, чтобы заполнение — единственная фаза, которой у
/// SIMD-ядра нет, — оставалось долей измеряемого.
const COLUMN_CELLS: u64 = 8_388_608;
const COLUMN_PASSES: u64 = 8;

// --- исходники: программа берётся у корпуса -------------------------------
//
// Ни одна из трёх нагрузок здесь не написана. Пункт 1 милестоуна волны 5
// требует, чтобы нагрузка была **программой в корпусе**, взятой понижением и
// сверенной с машиной, а корпусную программу прогоняет `tests/agreement.rs`
// договором трёх вычислителей. Размер при этом обязан различаться — машина не
// осилит полсотни миллионов витков, — и вот здесь заводился бы разъезд: две
// копии одной программы, из которых проверяется одна, а мерится другая.
//
// Копия поэтому одна. Стенд читает корпусный файл и переписывает в нём
// **только** строки размера ([`harness::resized`]), а имя, встретившееся не
// ровно один раз, роняет стенд. Правка ядра в корпусе меняет ответ и роняет
// сверку с соседом; правка соседа роняет её же.

/// Скалярный цикл: плоский счётчик, плоский накопитель, ноль ячеек кучи.
fn scalar_source(chain: Chain, turns: u64) -> String {
    resized(&corpus(chain.fixture()), &[("turns", turns)])
}

/// FBIP-цикл: список строится однажды, проходы переписывают его на месте.
fn fbip_source(cells: i64, passes: i64) -> String {
    let sizes = [
        ("cells", u64::try_from(cells).expect("ячеек не меньше нуля")),
        (
            "passes",
            u64::try_from(passes).expect("проходов не меньше нуля"),
        ),
    ];
    resized(&corpus("workload-fbip"), &sizes)
}

/// Скалярное ядро над колонкой: проход по плоскому `Float32`-массиву.
fn column_source(cells: u64, passes: u64) -> String {
    resized(
        &corpus("workload-column"),
        &[("cells", cells), ("passes", passes)],
    )
}

// --- понижение и машина --------------------------------------------------

/// Одна программа, два бэкенда: элаборация и специализация **общие**.
///
/// Так требует решение волны 0, вариант (а): второй эмиттер, а не второй
/// компилятор. Для замера это не архитектурная красота, а условие годности
/// числа — понизь стенд две программы, и отношение мерило бы расхождение
/// специализаций пополам с расхождением эмиттеров, а разделить их было бы
/// нечем.
struct Both {
    /// Порождённый C — единица трансляции целиком.
    c: String,
    /// `.ll` со спутником, либо названный отказ скалярного фрагмента.
    llvm: Result<Artefacts, adamas_codegen::CompileError>,
}

fn both(source: &str) -> Both {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = entry(&signature);
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .expect("специализация обязана пройти")
        .term;
    Both {
        c: adamas_codegen::compile(&signature, &made).expect("нагрузка обязана понижаться"),
        llvm: adamas_codegen::compile_llvm(&signature, &made),
    }
}

/// Порождённый C: специализация, понижение, эмиссия.
fn lowered(source: &str) -> String {
    both(source).c
}

/// Ответ машины, то есть `adamas eval`.
fn machine(source: &str) -> String {
    let (signature, _, _) = elaborated(source);
    let written = entry(&signature);
    adamas_interp::run(&signature, &written)
        .expect("чистая программа обязана считаться")
        .printed(Some(PRINT_DEPTH))
        .to_string()
}

/// Собранная нагрузка из исходника: понижение, сборка, прогон.
fn load(name: &str, source: &str) -> Load {
    Load::measured(
        name,
        built(&harness::scratch(STAND), name, &lowered(source)),
    )
}

/// Понижение отвечает то же, что машина, — на размере, который машине по силам.
fn agrees(name: &str, source: &str) {
    let expected = machine(source);
    let load = load(name, source);
    assert_eq!(
        load.answer, expected,
        "{name}: понижение посчитало не то, что машина"
    );
    assert_eq!(load.live, 0, "{name}: прогон оставил живые блоки");
}

// --- второй столбец: LLVM против C ----------------------------------------

/// Та же нагрузка LLVM-путём, либо названный отказ эмиттера.
///
/// Отказ **не** молчаливый пропуск: причина печатается, и строка таблицы
/// объявляется дырой. Скрыть её значило бы выдать отсутствие программы за
/// отсутствие разрыва.
fn llvm_load(
    backend: &Backend,
    name: &str,
    program: &Both,
    pipeline: &Pipeline,
    level: &str,
) -> Option<Load> {
    match &program.llvm {
        Ok(artefacts) => Some(backend.load(name, artefacts, pipeline, level)),
        Err(error) => {
            eprintln!("{name}: LLVM-эмиттер нагрузку не берёт: {error}");
            None
        }
    }
}

/// Нагрузка, собранная обоими бэкендами из **одного** понижения.
struct Sides {
    /// Исходник: свидетелям он нужен, чтобы пересобрать ту же программу иначе.
    source: String,
    c: Load,
    /// `None` — LLVM-эмиттер нагрузку не берёт, и причина напечатана.
    llvm: Option<Load>,
    /// Текст `.ll`: его читает свидетель схлопывания RC.
    ll: String,
}

fn sides(name: &str, source: &str, backend: Option<&Backend>) -> Sides {
    let program = both(source);
    let c = Load::measured(name, built(&harness::scratch(STAND), name, &program.c));
    let ll = program
        .llvm
        .as_ref()
        .map(|artefacts| artefacts.ll.clone())
        .unwrap_or_default();
    let llvm = backend.and_then(|backend| {
        llvm_load(
            backend,
            &format!("{name}-llvm"),
            &program,
            &backend.pipeline(),
            SUPPORT_LEVEL,
        )
    });
    if let Some(llvm) = &llvm {
        same_work(name, &c, llvm);
    }
    Sides {
        source: source.to_owned(),
        c,
        llvm,
        ll,
    }
}

/// Строка второго столбца, если LLVM-путь нагрузку берёт.
fn second_column(what: &str, load: &Sides, floor: &Sides) {
    let (Some(llvm), Some(llvm_floor)) = (&load.llvm, &floor.llvm) else {
        eprintln!("отношение/{what}: LLVM против C — строка не снята, нагрузку эмиттер не берёт");
        return;
    };
    llvm_against_c(
        what,
        &Column {
            llvm,
            llvm_floor,
            c: &load.c,
            c_floor: &floor.c,
            ll: &load.ll,
        },
    );
}

// --- сосед на Rust -------------------------------------------------------
//
// Оба соседа написаны **петлёй, а не самовызовом**, и это измерено, а не
// выбрано. Хвостовая рекурсия — та самая, какой обе нагрузки написаны на
// Adamas, — у rustc гарантии не имеет, и обрывается она в обе стороны: обход
// списка упал `SIGABRT` уже в release (освобождение `Box`, из которого
// значение вынуто, стоит после вызова, и вызов перестаёт быть последним
// действием), а скалярный `mix` — в debug, под `cargo test --all-targets`,
// где сворачивать хвост некому.
//
// Сравниваются поэтому две петли. У порождённого C она тоже получается —
// самовызов в хвосте эмиттер печатает обычным вызовом, а в петлю его
// сворачивает `-foptimize-sibling-calls`, — и вот это как раз проверено
// прогоном: [`SCALAR_TURNS`] витков ни одному стеку кадрами не покрыть.
// Кредита за несвёрнутый хвост соседа стенд себе не берёт: разной остаётся
// ровно та вещь, ради которой строка и мерится, — у соседа ячейка на элемент
// прохода, у понижения ноль.

/// Список эквивалентными формами данных: те же конструкторы, владение через
/// `Box`.
enum List {
    Nil,
    Cons(i64, Box<List>),
}

fn build(n: i64, xs: List) -> List {
    let mut xs = xs;
    let mut left = n;
    while left != 0 {
        xs = List::Cons(left, Box::new(xs));
        left -= 1;
    }
    xs
}

/// Проход: разобранная ячейка уходит в `free`, построенная берётся `Box::new`.
///
/// Переписать её на месте Rust не даёт, и это не свойство кода, а свойство
/// модели: reuse §5.1 держится на счётчике ссылок, которого у `Box` нет.
/// Порядок здесь тот же, что у понижения, — сперва освободить, потом взять, —
/// иначе аллокатор соседа не попадал бы в tcache там, где попадает наш.
fn step(xs: List, acc: List) -> List {
    let mut xs = xs;
    let mut acc = acc;
    while let List::Cons(x, rest) = xs {
        xs = *rest;
        acc = List::Cons(x.wrapping_add(1), Box::new(acc));
    }
    acc
}

fn turn(n: i64, xs: List) -> List {
    let mut xs = xs;
    for _ in 0..n {
        xs = step(xs, List::Nil);
    }
    xs
}

fn total(xs: List, acc: i64) -> i64 {
    let mut xs = xs;
    let mut acc = acc;
    while let List::Cons(x, rest) = xs {
        xs = *rest;
        acc = acc.wrapping_mul(3).wrapping_add(x);
    }
    acc
}

/// Множитель и слагаемое колонного ядра: те же числа, что в корпусной
/// программе. Разъезд ловится ответом на полном размере.
const GAIN: f32 = 1.03125;
const BIAS: f32 = 1.0;

/// Колонное ядро эквивалентным кодом: плоский буфер `f32`, тот же порядок,
/// та же индексация с проверкой границы.
///
/// Проверка границы стоит и у нас: `adamas_array_at` обрывает процесс на
/// номере вне длины (`array.c`), — поэтому `xs[at]` соседа, а не
/// `get_unchecked`, и есть эквивалентный код §6. Петля, а не самовызов, по той
/// же причине, что у прочих соседей стенда.
///
/// Буфер заводится с **явным** заполнением: `arrayNew` пишет нули в блок, а
/// `vec![0.0; n]` уходит в `calloc`, то есть в незаписанные страницы. Что
/// разница эта настоящая, а не съедается LLVM, измерено отдельной программой на
/// тех же размерах: `calloc` даёт пол 28.6 мс, `with_capacity` + `resize` —
/// 32.1, то есть проход обнуления стоит соседу 12%. Без этой строки он не
/// платил бы прохода, который платим мы.
fn column(cells: u64, passes: u64) -> f32 {
    let count = usize::try_from(cells).expect("длина колонки помещается в usize");
    let mut xs: Vec<f32> = Vec::with_capacity(count);
    xs.resize(count, 0.0);

    // Заполнение: ячейки различны, значение растёт, номер убывает.
    let mut value = 1.0_f32;
    let mut i = cells;
    while i != 0 {
        let at = usize::try_from(i - 1).expect("номер ячейки помещается в usize");
        xs[at] = value;
        value += 1.0;
        i -= 1;
    }

    // Ядро: element-wise по всей колонке, столько раз, сколько проходов.
    let mut left = passes;
    while left != 0 {
        let mut i = cells;
        while i != 0 {
            let at = usize::try_from(i - 1).expect("номер ячейки помещается в usize");
            xs[at] = xs[at] * GAIN + BIAS;
            i -= 1;
        }
        left -= 1;
    }

    // Свёртка вычитанием: чередующийся знак делает перестановку наблюдаемой.
    let mut acc = 0.0_f32;
    let mut i = cells;
    while i != 0 {
        let at = usize::try_from(i - 1).expect("номер ячейки помещается в usize");
        acc = xs[at] - acc;
        i -= 1;
    }
    acc
}

/// Дочерний прогон соседа, если стенд запущен им.
///
/// Запрос — имя нагрузки и её размеры через двоеточие: `scalar:<витков>`,
/// `scalar-affine:<витков>`, `fbip:<ячеек>:<проходов>`,
/// `column:<ячеек>:<проходов>`.
fn as_child() -> bool {
    let Ok(request) = std::env::var(NEIGHBOUR) else {
        return false;
    };
    let mut field = request.split(':');
    let kind = field.next().expect("у запроса есть имя нагрузки");
    let number = |field: Option<&str>| -> i64 {
        field
            .expect("размер нагрузки назван")
            .parse()
            .expect("размер нагрузки — число")
    };
    let word = |field: Option<&str>| -> u64 {
        u64::try_from(number(field)).expect("размер не меньше нуля")
    };
    if let Some(chain) = Chain::ALL.into_iter().find(|chain| chain.name() == kind) {
        let turns = number(field.next());
        println!(
            "{}",
            chain.mix(u64::try_from(turns).expect("витков не меньше нуля"))
        );
        return true;
    }
    match kind {
        "fbip" => {
            let cells = number(field.next());
            let passes = number(field.next());
            println!("{}", total(turn(passes, build(cells, List::Nil)), 0));
        }
        "column" => {
            let cells = word(field.next());
            let passes = word(field.next());
            // `{:?}`, а не `{}`: печать `Float32` у понижения повторяет
            // кратчайшую запись Rust (`flat.c`), и сверять надо с ней.
            println!("{:?}", column(cells, passes));
        }
        other => panic!("стенд не знает нагрузки `{other}`"),
    }
    true
}

// --- замеры --------------------------------------------------------------

/// Скалярная арифметика: первая нагрузка трека Z, обеими цепочками.
fn scalar(criterion: &mut Criterion) {
    two_chains_differ_by_one_line();
    let backend = Backend::new(STAND);
    for chain in Chain::ALL {
        one_chain(criterion, chain, backend.as_ref());
    }
}

/// Две скалярные фикстуры расходятся ровно одной строкой кода.
///
/// Строки 1а и 1б таблицы существуют затем, чтобы различаться **одним
/// умножением**, и вывод про переассоциацию держится на том, что всё
/// остальное у них общее. Держать это глазом нельзя: два файла в корпусе —
/// два места, где можно поправить одно и забыть другое. Сравниваются строки
/// кода; комментарии у файлов свои и расходиться им положено.
fn two_chains_differ_by_one_line() {
    let code = |name: &str| -> Vec<String> {
        corpus(name)
            .lines()
            .map(str::trim_end)
            .filter(|line| !line.is_empty() && !line.starts_with("--"))
            .map(str::to_owned)
            .collect()
    };
    let (left, right) = (
        code(Chain::Squaring.fixture()),
        code(Chain::Affine.fixture()),
    );
    assert_eq!(
        left.len(),
        right.len(),
        "у скалярных фикстур разное число строк кода: сравнивать их построчно нечем"
    );
    let apart: Vec<(&String, &String)> = left
        .iter()
        .zip(right.iter())
        .filter(|(left, right)| left != right)
        .collect();
    assert_eq!(
        apart.len(),
        1,
        "скалярные фикстуры расходятся не одной строкой, а {}: {apart:#?}",
        apart.len()
    );
}

/// Одна форма цепочки: пол, работа, сосед, отношение.
fn one_chain(criterion: &mut Criterion, chain: Chain, backend: Option<&Backend>) {
    let name = chain.name();
    let mut group = criterion.benchmark_group(name);
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);

    // Сверяется корпусный файл **как он есть**, без подстановки: то, что
    // прогоняет машина, и то, что понижает стенд, обязано быть одним текстом.
    agrees(&format!("{name}-small"), &corpus(chain.fixture()));

    // Пол — та же программа без работы; свой у каждой стороны, потому что
    // двоичных файлов два (а с LLVM-столбцом — три).
    let floor = sides(&format!("{name}-floor"), &scalar_source(chain, 0), backend);
    let idle = format!("{name}:0");
    group.bench_function("floor", |bencher| {
        by_floor(bencher, || drop(ran(&floor.c.binary)));
    });
    group.bench_function("rust/floor", |bencher| {
        by_floor(bencher, || drop(ran_neighbour(&idle)));
    });

    let load = sides(name, &scalar_source(chain, SCALAR_TURNS), backend);
    // Плоский счётчик наблюдаем здесь: индуктивный дал бы ячейку на виток.
    assert_eq!(
        load.c.allocated, 0,
        "{name}: скалярный цикл выдал блоки — счётчик или накопитель перестал \
         быть плоским"
    );
    let request = format!("{name}:{SCALAR_TURNS}");
    let (stdout, _) = ran_neighbour(&request);
    assert_eq!(
        stdout.trim(),
        load.c.answer,
        "{name}: сосед на Rust считает не тот же цикл"
    );

    group.bench_function("native", |bencher| {
        by_floor(bencher, || drop(ran(&load.c.binary)));
    });
    group.bench_function("rust", |bencher| {
        by_floor(bencher, || drop(ran_neighbour(&request)));
    });
    if let (Some(llvm), Some(llvm_floor)) = (&load.llvm, &floor.llvm) {
        group.bench_function("llvm", |bencher| {
            by_floor(bencher, || drop(ran(&llvm.binary)));
        });
        group.bench_function("llvm/floor", |bencher| {
            by_floor(bencher, || drop(ran(&llvm_floor.binary)));
        });
    }
    group.finish();

    // Число строки таблицы берётся здесь, а не у отчёта: см. [`ratio`].
    ratio(
        name,
        || drop(ran(&load.c.binary)),
        || drop(ran(&floor.c.binary)),
        || drop(ran_neighbour(&request)),
        || drop(ran_neighbour(&idle)),
    );
    second_column(name, &load, &floor);
    second_column_witnesses(name, backend, &load, &floor);
}

/// FBIP-цикл: третья нагрузка трека Z.
fn fbip(criterion: &mut Criterion) {
    let backend = Backend::new(STAND);
    let mut group = criterion.benchmark_group("fbip");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);

    agrees("fbip-small", &corpus("workload-fbip"));

    let floor = sides("fbip-floor", &fbip_source(0, 0), backend.as_ref());
    group.bench_function("floor", |bencher| {
        by_floor(bencher, || drop(ran(&floor.c.binary)));
    });
    group.bench_function("rust/floor", |bencher| {
        by_floor(bencher, || drop(ran_neighbour("fbip:0:0")));
    });

    let load = sides(
        "fbip",
        &fbip_source(FBIP_CELLS, FBIP_PASSES),
        backend.as_ref(),
    );
    // Единственные выданные ячейки — те, что построил `build`. Все проходы
    // переписывают их на месте, и это утверждение, а не наблюдение: сломанный
    // reuse уронит стенд здесь. Для LLVM-стороны то же утверждение делает
    // [`same_work`]: счётчики двух бэкендов обязаны совпасть поштучно.
    assert_eq!(
        load.c.allocated,
        usize::try_from(FBIP_CELLS).expect("ячеек не меньше нуля"),
        "проход выдал ячейки — reuse §5.1 не сработал"
    );
    let request = format!("fbip:{FBIP_CELLS}:{FBIP_PASSES}");
    let (stdout, _) = ran_neighbour(&request);
    assert_eq!(
        stdout.trim(),
        load.c.answer,
        "сосед на Rust считает не тот же цикл"
    );

    group.bench_function("native", |bencher| {
        by_floor(bencher, || drop(ran(&load.c.binary)));
    });
    group.bench_function("rust", |bencher| {
        by_floor(bencher, || drop(ran_neighbour(&request)));
    });
    if let (Some(llvm), Some(llvm_floor)) = (&load.llvm, &floor.llvm) {
        group.bench_function("llvm", |bencher| {
            by_floor(bencher, || drop(ran(&llvm.binary)));
        });
        group.bench_function("llvm/floor", |bencher| {
            by_floor(bencher, || drop(ran(&llvm_floor.binary)));
        });
    }
    group.finish();

    ratio(
        "FBIP-цикл",
        || drop(ran(&load.c.binary)),
        || drop(ran(&floor.c.binary)),
        || drop(ran_neighbour(&request)),
        || drop(ran_neighbour("fbip:0:0")),
    );
    second_column("FBIP-цикл", &load, &floor);
    second_column_witnesses("FBIP-цикл", backend.as_ref(), &load, &floor);
}

// --- свидетели второго столбца --------------------------------------------

/// Свидетели строки второго столбца: сами свидетели живут в заготовке, здесь
/// только пересборка той же программы — она у стендов своя.
fn second_column_witnesses(what: &str, backend: Option<&Backend>, load: &Sides, floor: &Sides) {
    let (Some(backend), Some(llvm), Some(llvm_floor)) = (backend, &load.llvm, &floor.llvm) else {
        return;
    };
    harness::witnesses(
        what,
        backend,
        &Column {
            llvm,
            llvm_floor,
            c: &load.c,
            c_floor: &floor.c,
            ll: &load.ll,
        },
        |stem, pipeline, support| {
            let side = llvm_load(backend, stem, &both(&load.source), pipeline, support)
                .expect("нагрузку эмиттер уже взял выше");
            let side_floor = llvm_load(
                backend,
                &format!("{stem}-floor"),
                &both(&floor.source),
                pipeline,
                support,
            )
            .expect("пол эмиттер уже взял выше");
            (side, side_floor)
        },
        |stem| {
            let dir = harness::scratch(STAND);
            (
                Load::measured(
                    stem,
                    harness::built_apart(&dir, stem, &both(&load.source).c),
                ),
                Load::measured(
                    &format!("{stem}-floor"),
                    harness::built_apart(&dir, &format!("{stem}-floor"), &both(&floor.source).c),
                ),
            )
        },
    );
}

/// Строка 4а второго столбца пуста, и пуста она **массивом**.
///
/// Утверждение, а не примечание к таблице. LLVM-эмиттер массивов не берёт
/// (названная граница треков A и A′), и колонное ядро на нём не собирается ни в
/// скалярном виде, ни в векторном. Начни он их брать — утверждение упадёт, и
/// дыру придётся закрывать числом, а не строкой в документе. Отсутствие
/// строки, оставленное молча, — тот самый обманчивый свидетель: читателю
/// таблицы его не отличить от «разрыва нет».
fn the_llvm_path_has_no_arrays() {
    let program = both(&column_source(8, 3));
    let why = program
        .llvm
        .err()
        .map(|error| error.to_string())
        .expect("колонное ядро на LLVM-пути не собирается: массивов у эмиттера нет");
    assert!(
        why.contains("массив"),
        "колонное ядро отвергнуто не массивом, а «{why}»: строка 4а пуста по \
         другой причине, чем записано"
    );
    eprintln!("колонное ядро: LLVM-столбец пуст — {why}");
}

/// Скалярное ядро над колонкой: четвёртая нагрузка трека Z без самой `Simd`.
fn column_kernel(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("column");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);

    agrees("column-small", &corpus("workload-column"));
    the_llvm_path_has_no_arrays();

    let floor = load("column-floor", &column_source(0, 0));
    group.bench_function("floor", |bencher| {
        by_floor(bencher, || drop(ran(&floor.binary)));
    });
    group.bench_function("rust/floor", |bencher| {
        by_floor(bencher, || drop(ran_neighbour("column:0:0")));
    });

    let load = load("column", &column_source(COLUMN_CELLS, COLUMN_PASSES));
    // Блок **один** на всю программу, сколько бы проходов ни было: колонка
    // плоская (§4.11), а `arraySet` переписывает уникальный блок по месту.
    // Утверждение, а не наблюдение: скопируй ядро колонку на каждом витке — и
    // строка мерила бы аллокатор, а не проход.
    assert_eq!(
        load.allocated, 1,
        "колонное ядро выдало не один блок: `arraySet` перестал писать по месту"
    );
    let request = format!("column:{COLUMN_CELLS}:{COLUMN_PASSES}");
    let (stdout, _) = ran_neighbour(&request);
    assert_eq!(
        stdout.trim(),
        load.answer,
        "сосед на Rust считает не то же ядро"
    );

    group.bench_function("native", |bencher| {
        by_floor(bencher, || drop(ran(&load.binary)));
    });
    group.bench_function("rust", |bencher| {
        by_floor(bencher, || drop(ran_neighbour(&request)));
    });
    group.finish();

    ratio(
        "колонное ядро",
        || drop(ran(&load.binary)),
        || drop(ran(&floor.binary)),
        || drop(ran_neighbour(&request)),
        || drop(ran_neighbour("column:0:0")),
    );
}

criterion_group!(benches, scalar, fbip, column_kernel);

/// `main` написан руками, а не взят у `criterion_main!`: дочерний прогон
/// соседа ([`as_child`]) обязан отвечать раньше, чем criterion разберёт
/// аргументы. Остальное — дословно то, во что разворачивается макрос.
fn main() {
    if as_child() {
        return;
    }
    benches();
    Criterion::default().configure_from_args().final_summary();
}
