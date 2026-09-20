//! Представление чужого указателя на границе Adamas↔C (§5.3, трек A волны 1
//! Фазы 8).
//!
//! Свидетель отвечает на три вопроса и ни на один сверх. **Берут ли уклад оба
//! понижения** - C-эмиттер и текстовый `.ll`, - и проверяется это прогоном до
//! линковки, а не чтением: неизвестное имя `llvm.*` восемнадцатая версия
//! принимает молча как внешнюю функцию (`tests/llvm.rs`,
//! `the_reader_of_the_minimum_llvm_is_blind_to_an_unknown_intrinsic`), и
//! «собралось» значило бы только «разобралось». **Чего уклад стоит в ячейках
//! кучи** - счётчиком рантайма, а не рассуждением. И **какое обязательство
//! уклад создаёт** - тоже прогоном: у сдвинутого непосредственного граница
//! адреса предъявляется, а не оговаривается.
//!
//! Исходники стенда лежат в `benches/boundary/`, рядом со стендом, который их
//! мерит. Второй копии здесь нет намеренно: разъехавшись, копии мерили бы одно,
//! а проверяли другое, и заметить это было бы нечем.
//!
//! Чего здесь нет: слова `extern` в языке (трек B), хождения машины наружу
//! (трек C) и линковки с настоящей библиотекой (трек D). Граница написана в
//! обход поверхностного языка - узла IR под внешний вызов сегодня нет вовсе,
//! и заводит его трек B.
//!
//! # Мутанты, которыми это мерено (2026-09-20)
//!
//! Таблица снята прогоном `cargo test -p adamas-codegen --test foreign` на
//! каждой правке порознь, с возвратом между ними; счёт - упавших свидетелей из
//! шести. Контроль на чистом дереве - ноль.
//!
//! | Мутант | Красных |
//! |---|---|
//! | `entry.c`, уклад IMM: взять `value` без `adamas_imm_get` | 4 |
//! | `entry.c`, уклад BOXED: вынести `adamas_alloc` из цикла | 2 |
//! | `entry.c`, уклад FLAT: пропустить вызов через границу | 3 |
//! | `boxed.ll`: `getelementptr` → `getelementptr inbounds nuw` | 1 |
//! | `imm.ll`: `shl … 1` → `shl … 2` | 2 |
//! | `boxed.ll`: смещение слота 8 → 16 | **0** |
//! | `imm.ll`: `ashr` → `lshr` | **0** |
//! | `probe.c`: снять `it->calls += 1` | **0** |
//!
//! Три выживших, и все три названы, а не заметены.
//!
//! *Смещение слота - симметричный путь.* Пишет и читает уклад одно и то же
//! место, поэтому смещение мимо слота даёт ту же величину обратно; шестнадцать
//! байт от начала - запись за концом блока, но `malloc` выдаёт больше
//! запрошенного, и прогон не спотыкается. Жанр этот в дереве уже назван
//! (`tests/boundary.rs`, шапка), и пинает смещение не этот стенд, а сам
//! эмиттер: он печатает `HEADER_BYTES + slot * SLOT_BYTES`, а совпадение этих
//! чисел с `adamas.h` проверяет `_Static_assert` в спутнике
//! (`emit_llvm.rs`, «Что объектный слой знает о раскладке»). Здесь константа
//! **списана** оттуда, и списанность - всё, что стенд о ней утверждает.
//!
//! *`ashr` против `lshr` неразличимы, и это свойство уклада (б), а не
//! свидетеля.* У адреса user-space старшие биты нулевые, поэтому знаковый и
//! беззнаковый сдвиг вправо дают одно и то же; различил бы их только адрес
//! выше 2^62, а такого на этой платформе не бывает. Отсюда прямое следствие
//! для решения: у (б) **нет** свидетеля, который поймал бы путаницу
//! знаковости, пока платформа даёт узкие адреса, - поймает её первый же
//! перенос. Границу адреса свидетель поэтому предъявляет прямо
//! ([`the_shifted_immediate_loses_the_address_above_two_to_the_sixty_second`]).
//!
//! *Счётчик походов в чужой библиотеке выжил* потому, что свёрнут он в ответ
//! **у всех четырёх укладов одинаково**: сними его - и все четверо ответят
//! одним и тем же другим числом. Ловит он не это, а уклад, сходивший за
//! границу не столько раз, сколько прочие, - и мутант на него стоит строкой
//! FLAT.

// Рантайм читается как ABI - ровно тот случай, ради которого `unsafe_code`
// объявлен `deny`, а не `forbid` (корневой `Cargo.toml`).
#![allow(unsafe_code)]
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use adamas_codegen::llvm::{Pipeline, Toolchain};

/// Уклады, написанные на C: имя и номер для `-DSHAPE=`.
///
/// Четыре, а не три: развилка (а) распадается на «коробка на каждое
/// пересечение» и «коробка одна, живёт полем `resource`», и цена у них разная
/// в разы. Мерить (а) одним числом значило бы назвать её дороже, чем она есть.
const SHAPES: [(&str, u32); 4] = [("boxed", 1), ("held", 2), ("imm", 3), ("flat", 4)];

/// Уклады, написанные текстовым `.ll`: три развилки плана как они есть.
const LOWERED: [&str; 3] = ["boxed", "imm", "flat"];

/// Сколько раз свидетель ходит за границу.
///
/// Мало: свидетелю нужен ответ, а не наносекунды. Больше берёт
/// `benches/foreign.rs`.
const CALLS: u64 = 10_000;

/// Исходники стенда: они же у бенчмарка.
fn boundary() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("benches/boundary")
}

/// Место под объектники и бинари этого свидетеля.
fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join("foreign");
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Ключи сборки свидетеля: `-O1` без межмодульной оптимизации.
///
/// Свидетелю нужен ответ, а не скорость, и разъехаться со строкой замера ему
/// нечем - числа он не печатает. `-Werror=implicit-function-declaration` ловит
/// расхождение с заголовком рантайма отказом сборки, а не молчанием.
const FLAGS: [&str; 5] = [
    "-std=c11",
    "-O1",
    "-Wall",
    "-Wno-unused",
    "-Werror=implicit-function-declaration",
];

/// Зовёт компилятор и роняет прогон его же выводом.
fn run(command: &mut Command, what: &str) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{what}: не собралось\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Объектники рантайма: собираются однажды на весь прогон.
///
/// Список приходит от самого рантайма (`build.rs`), а не написан здесь: вторая
/// копия разъезжалась бы молча, и новый слой давал бы «undefined reference».
fn runtime() -> &'static [PathBuf] {
    static OBJECTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    OBJECTS.get_or_init(|| {
        let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
        let dir = scratch();
        env!("ADAMAS_RUNTIME_UNITS")
            .split(',')
            .map(|name| {
                let object = dir.join(format!("rt-{name}.o"));
                run(
                    Command::new(env!("ADAMAS_CC"))
                        .args(FLAGS)
                        .arg("-c")
                        .arg("-I")
                        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
                        .arg(sources.join(name))
                        .arg("-o")
                        .arg(&object),
                    name,
                );
                object
            })
            .collect()
    })
}

/// Чужая библиотека и точка входа: два объектника, общие всем укладам.
///
/// Чужая библиотека собирается **без** заголовка рантайма и без его ключей: она
/// и есть то, о чём Adamas ничего не знает.
fn shared() -> &'static (PathBuf, PathBuf) {
    static PAIR: OnceLock<(PathBuf, PathBuf)> = OnceLock::new();
    PAIR.get_or_init(|| {
        let dir = scratch();
        let probe = dir.join("probe.o");
        run(
            Command::new(env!("ADAMAS_CC"))
                .args(["-std=c11", "-O1", "-Wall"])
                .arg("-c")
                .arg(boundary().join("probe.c"))
                .arg("-o")
                .arg(&probe),
            "probe.c",
        );
        let entry = dir.join("main.o");
        run(
            Command::new(env!("ADAMAS_CC"))
                .args(FLAGS)
                .arg("-c")
                .arg("-I")
                .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
                .arg(boundary().join("main.c"))
                .arg("-o")
                .arg(&entry),
            "main.c",
        );
        (probe, entry)
    })
}

/// Линкует уклад с чужой библиотекой, точкой входа и рантаймом.
fn linked(stem: &str, object: &Path) -> PathBuf {
    let dir = scratch();
    let binary = dir.join(stem);
    let (probe, entry) = shared();
    run(
        Command::new(env!("ADAMAS_CC"))
            .arg(object)
            .arg(entry)
            .arg(probe)
            .args(runtime())
            .arg("-o")
            .arg(&binary),
        stem,
    );
    binary
}

/// Уклад, понижённый в C.
fn in_c(name: &str, shape: u32) -> PathBuf {
    let dir = scratch();
    let object = dir.join(format!("c-{name}.o"));
    run(
        Command::new(env!("ADAMAS_CC"))
            .args(FLAGS)
            .arg(format!("-DSHAPE={shape}"))
            .arg("-c")
            .arg("-I")
            .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
            .arg(boundary().join("entry.c"))
            .arg("-o")
            .arg(&object),
        name,
    );
    linked(&format!("c-{name}"), &object)
}

/// Уклад, понижённый в текстовый `.ll`, названной цепочкой инструментов.
///
/// Конвейер тот же, каким пользуется эмиттер, - `llvm-as`, `opt -O2`,
/// `llc -O2` ([`Pipeline::optimised`]), - и доходит он до линковки: разбором
/// проверялось бы только то, что текст разобрался.
fn in_llvm(tools: &Toolchain, tag: &str, name: &str) -> PathBuf {
    let dir = scratch();
    let stem = format!("{tag}-{name}");
    let text = dir.join(format!("{stem}.ll"));
    std::fs::copy(boundary().join(format!("{name}.ll")), &text).unwrap();
    let object = Pipeline::optimised()
        .run(tools, &text, &stem)
        .unwrap_or_else(|error| panic!("{stem}: конвейер LLVM отказал: {error}"));
    linked(&stem, &object)
}

/// Прогон уклада: ответ со stdout, «выдано» и «живо» со stderr.
fn ran(binary: &Path, calls: u64) -> (String, usize, usize) {
    let output = Command::new(binary)
        .arg(calls.to_string())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}: прогон оборвался: {}",
        binary.display(),
        output.status
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    let numbers: Vec<usize> = stderr
        .split_whitespace()
        .filter_map(|word| word.trim_end_matches(',').parse().ok())
        .collect();
    assert_eq!(
        numbers.len(),
        2,
        "{}: счётчики блоков не прочитались из `{}`",
        binary.display(),
        stderr.trim_end()
    );
    let answer = String::from_utf8(output.stdout).unwrap();
    (answer.trim_end().to_owned(), numbers[0], numbers[1])
}

/// Собранные уклады какой-то одной стороны: имя и бинарь.
type Built = Vec<(&'static str, PathBuf)>;

/// Уклады, понижённые в C.
///
/// Собираются **однажды на весь прогон**, и это не ускорение. Свидетели идут
/// потоками одного процесса, а уклад у них общий: собери его каждый заново - и
/// один поток переписывал бы бинарь, который другой в эту минуту исполняет
/// («Text file busy», поймано первым же прогоном).
fn compiled() -> &'static Built {
    static IT: OnceLock<Built> = OnceLock::new();
    IT.get_or_init(|| {
        SHAPES
            .into_iter()
            .map(|(name, shape)| (name, in_c(name, shape)))
            .collect()
    })
}

/// Уклады, понижённые текстовым `.ll` текущей цепочкой.
///
/// Своя ячейка, а не поле общего стенда, и это **условие осмысленности
/// таблицы мутантов**: сложи три стороны в одну ячейку - и отказ разбора у
/// восемнадцатой версии ронял бы заодно свидетелей, о понижении в LLVM не
/// спрашивающих (поймано мутантом `getelementptr inbounds nuw`: четыре красных
/// вместо одного).
fn lowered_current() -> &'static Built {
    static IT: OnceLock<Built> = OnceLock::new();
    IT.get_or_init(|| match toolchains() {
        Some((current, _)) => LOWERED
            .into_iter()
            .map(|name| (name, in_llvm(&current, "cur", name)))
            .collect(),
        None => Vec::new(),
    })
}

/// Они же минимальной поддерживаемой цепочкой.
fn lowered_minimum() -> &'static Built {
    static IT: OnceLock<Built> = OnceLock::new();
    IT.get_or_init(|| match toolchains() {
        Some((_, minimum)) => LOWERED
            .into_iter()
            .map(|name| (name, in_llvm(&minimum, "min", name)))
            .collect(),
        None => Vec::new(),
    })
}

/// Бинарь уклада, понижённого в C.
fn c_binary(name: &str) -> &'static Path {
    compiled()
        .iter()
        .find(|it| it.0 == name)
        .unwrap_or_else(|| panic!("уклада {name} нет в стенде"))
        .1
        .as_path()
}

/// Цепочки LLVM: текущая и минимальная поддерживаемая.
///
/// Правило то же, что у прочих свидетелей понижения: инструмента нет - прогон
/// падает, а не молчит; молчаливый пропуск дал бы зелёный свидетель, ничего не
/// проверивший.
fn toolchains() -> Option<(Toolchain, Toolchain)> {
    if std::env::var("ADAMAS_LLVM").is_ok_and(|it| it == "absent") {
        eprintln!("LLVM объявлен отсутствующим (ADAMAS_LLVM=absent): понижение не проверялось");
        return None;
    }
    Some((
        Toolchain::from_variable(adamas_codegen::llvm::TOOLS_VARIABLE),
        Toolchain::from_variable(adamas_codegen::llvm::MINIMUM_TOOLS_VARIABLE),
    ))
}

/// Все четыре уклада отвечают одним числом.
///
/// В ответ свёрнуто число походов за границу (`adamas_probe_calls`), поэтому
/// уклад, сходивший наружу не столько раз, сколько прочие, отвечает **иначе**,
/// а не «тоже верно».
#[test]
fn all_four_shapes_answer_the_same_number() {
    let mut answers = Vec::new();
    for (name, binary) in compiled() {
        let (answer, _, live) = ran(binary, CALLS);
        assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
        answers.push((name, answer));
    }
    let (first, want) = &answers[0];
    for (name, got) in &answers[1..] {
        assert_eq!(got, want, "{name} ответил не то, что {first}");
    }
}

/// Ячейки кучи выдаёт только коробка, и ровно столько, сколько пересечений.
///
/// Это и есть цена развилки (а), и она **считана**, а не названа: у уклада «на
/// каждое пересечение» ячеек столько же, сколько вызовов, у уклада `resource` -
/// одна на весь прогон, у сдвинутого непосредственного и у плоского слова - ни
/// одной. Чужая библиотека считает собственный `malloc` мимо этого счётчика
/// (`probe.c`), поэтому число здесь - ровно цена уклада.
#[test]
fn only_the_box_spends_a_cell() {
    let crossings = usize::try_from(CALLS).unwrap();
    for (name, want) in [("boxed", crossings), ("held", 1), ("imm", 0), ("flat", 0)] {
        let (_, allocated, live) = ran(c_binary(name), CALLS);
        assert_eq!(allocated, want, "{name}: ячеек выдано не столько");
        assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    }
}

/// Каждый уклад выразим **обоими** понижениями, и оба дают один ответ.
///
/// Текстовый `.ll` ограничивает сильнее, чем C, поэтому проверка идёт до
/// линковки и прогона: собранное значило бы «разобралось», а не «работает».
#[test]
fn both_lowerings_take_every_shape() {
    if toolchains().is_none() {
        return;
    }
    assert_eq!(
        lowered_current().len(),
        LOWERED.len(),
        "понижений в стенде меньше, чем укладов: свидетель был бы зелен ни от чего"
    );
    for (name, binary) in lowered_current() {
        let (want, want_allocated, _) = ran(c_binary(name), CALLS);
        let (got, got_allocated, live) = ran(binary, CALLS);
        assert_eq!(got, want, "{name}: понижения ответили разное");
        assert_eq!(
            got_allocated, want_allocated,
            "{name}: понижения выдали разное число ячеек"
        );
        assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    }
}

/// Тот же текст читается минимальной поддерживаемой версией LLVM.
///
/// Правило консервативного подмножества (`emit_llvm.rs`, шапка модуля)
/// проверяется прогоном на `MINIMUM_MAJOR`, а не грепом по формам: греп по
/// формам врал трижды подряд. Проверяется здесь и **поведение**, а не только
/// разбор, - потому прогон идёт до ответа.
#[test]
fn the_minimum_llvm_reads_every_shape() {
    if toolchains().is_none() {
        return;
    }
    assert_eq!(
        lowered_minimum().len(),
        LOWERED.len(),
        "понижений в стенде меньше, чем укладов: свидетель был бы зелен ни от чего"
    );
    for (name, binary) in lowered_minimum() {
        let (want, _, _) = ran(c_binary(name), CALLS);
        let (got, _, live) = ran(binary, CALLS);
        assert_eq!(got, want, "{name}: минимальная версия ответила иначе");
        assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    }
}

/// Чужой указатель неотличим от объекта кучи: младший бит у него нулевой.
///
/// Посылка трека, предъявленная прогоном: положить `void *` в `adamas_value`
/// как есть нельзя, потому что первый же `adamas_dup` пойдёт читать заголовок
/// по чужому адресу.
#[test]
fn a_foreign_pointer_is_indistinguishable_from_a_heap_object() {
    let it = Box::new(0_u64);
    let address = std::ptr::from_ref::<u64>(&*it).cast::<adamas_runtime::ffi::Object>();
    // SAFETY: `adamas_is_imm` читает младший бит слова и по адресу не ходит.
    let immediate = unsafe { adamas_runtime::ffi::adamas_is_imm(address.cast_mut()) };
    assert_eq!(
        immediate, 0,
        "адрес кучи опознан непосредственным: посылка трека неверна"
    );
    drop(it);
}

/// Сдвинутое непосредственное теряет адрес начиная с 2^62.
///
/// Обязательство развилки (б), предъявленное **прогоном**, а не оговоркой.
/// `adamas_imm` есть `(p << 1) | 1`, `adamas_imm_get` - арифметический сдвиг
/// вправо; у адреса с выставленным 62-м битом сдвиг влево занимает знаковый, и
/// обратный сдвиг возвращает не то, что клали. Адреса user-space Linux сегодня
/// меньше 2^47, но это свойство платформы, а не языка, и уклад (б) обязан
/// записать его обязательством.
#[test]
fn the_shifted_immediate_loses_the_address_above_two_to_the_sixty_second() {
    let fits: isize = 0x0000_4000_0000_0000;
    let over: isize = 0x4000_0000_0000_0000;
    // SAFETY: обе функции считают биты слова и по адресу не ходят.
    let (there, back) = unsafe {
        (
            adamas_runtime::ffi::adamas_imm_get(adamas_runtime::ffi::adamas_imm(fits)),
            adamas_runtime::ffi::adamas_imm_get(adamas_runtime::ffi::adamas_imm(over)),
        )
    };
    assert_eq!(there, fits, "адрес user-space не пережил сдвига");
    assert_ne!(
        back, over,
        "адрес с 62-м битом пережил сдвиг: границы 2^62 у уклада (б) нет"
    );
}
