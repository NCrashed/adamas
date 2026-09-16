//! Разделяемая половина гибридного счётчика не стоит на горячем витке (§5.1).
//!
//! Счётчик ссылок гибриден: локальное значение считается неатомарно,
//! разделяемое - атомарно, и различает их флаг `ADAMAS_FLAG_SHARED` в
//! заголовке (трек I волны 2 Фазы 7). Ветвь по флагу стоит в тех же точках
//! входа, через которые идёт весь RC-трафик, - то есть на горячем витке всякой
//! чужой нагрузки.
//!
//! # Зачем свидетель заведён
//!
//! Потому что один раз эта ветвь уже стоила **1.64 раза** колонному ядру
//! (строка 4а `docs/measurements/workload-gap/`), и ни один свидетель этого не
//! поймал: свидетели трека I считают ответы и гонки, а времени не смотрит ни
//! один. Регрессия прошла все ворота и всплыла через фазу, у сквозного
//! перемера. Правило «правка рантайма, попадающая на горячий путь, обязана
//! мериться нагрузкой из таблицы разрыва» само по себе ничего не ловит: оно
//! текст. Ловит - число, и вот оно.
//!
//! # Что именно проверяется, и почему это, а не время
//!
//! Полный замер по методике требует тихой машины и пяти прогонов; ворота
//! гоняются на занятой и обязаны быть быстрыми. Свидетель поэтому **счётный**,
//! и считает он не время, а атомарные операции **внутри тела** точки входа.
//!
//! Место выбрано замером, а не вкусом (§10 вопрос 175, 2026-09-16). Мерены
//! четыре сборки одного и того же порождённого C, различающиеся одной вещью:
//!
//! | рантайм | колонное ядро |
//! |---|---|
//! | как был у трека I | 181.4 мс |
//! | он же плюс `__builtin_expect` на ветви | 180.6 мс |
//! | атомарная операция вынесена за `noinline` | **117.6 мс** |
//! | ветвь снята целиком (потолок, атомарности нет) | 109.6 мс |
//!
//! Читается это так: **переход не стоит ничего**, подсказка о его вероятности
//! не двигает число вовсе. Стоит атомарная операция, **оставленная в теле**:
//! с ней gcc отказывается делить `adamas_array_writable` на горячую половину и
//! холодную, и виток зовёт всю функцию целиком; унеси её - деление
//! возвращается. Наблюдаемое отсюда и взято: атомарной операции в теле точки
//! входа быть не должно.
//!
//! Размер тела наблюдаемым **не** годится, и это тоже замерено: у
//! `adamas_is_unique` он 19 инструкций IR против 17, то есть решение инлайнера
//! переворачивается на разнице в две инструкции. Потолок по размеру либо
//! пропустил бы регрессию, либо падал бы от любой правки.
//!
//! # Почему в этом крейте, а рантайм в другом
//!
//! Проверяется свойство рантайма, а защищается им число **таблицы разрыва** -
//! стенда этого крейта. Здесь же живёт единственная запись правила «свидетеля
//! LLVM, которого нет, объявляют отсутствующим в одном месте»
//! ([`harness::llvm_toolchains`]); второй её копии быть не должно.
//!
//! Читается IR, а не машинный код: `acquire`-загрузка на x86 есть обычный
//! `mov`, и в дизассемблере её от неатомарной не отличить ничем. В IR она
//! `load atomic`.

mod harness;

use std::path::{Path, PathBuf};
use std::process::Command;

/// Точки входа, через которые идёт RC-трафик: у каждой ветвь по флагу.
///
/// Список, а не «все функции с атомарной операцией»: атомарные операции есть и
/// у реестра блоков (`enlist`, `adamas_stat_live_everywhere`), они там по делу
/// и на витке пользовательской программы не стоят.
const HOT: [&str; 5] = [
    "adamas_rc",
    "adamas_dup",
    "adamas_is_unique",
    "adamas_drop",
    "adamas_drop_reuse",
];

/// Точка входа и её разделяемая половина.
///
/// Половин четыре на пять точек: `adamas_drop` и `adamas_drop_reuse` отдают
/// ссылку одним и тем же `released`, и половина у них общая.
const PAIRS: [(&str, &str); 5] = [
    ("adamas_rc", "adamas_rc_shared"),
    ("adamas_dup", "adamas_dup_shared"),
    ("adamas_is_unique", "adamas_unique_shared"),
    ("adamas_drop", "adamas_released_shared"),
    ("adamas_drop_reuse", "adamas_released_shared"),
];

/// Разделяемые половины: каждая обязана быть отдельной и не инлайниться.
const HALVES: [&str; 4] = [
    "adamas_rc_shared",
    "adamas_dup_shared",
    "adamas_unique_shared",
    "adamas_released_shared",
];

/// Тело точки входа не содержит атомарной операции ни одной.
#[test]
fn the_shared_half_stays_out_of_the_body() {
    // Стебель свой у каждого теста: они идут потоками одного двоичного файла, а
    // артефакт лежит на диске - общий стебель дал бы гонку двух `clang`.
    let Some(text) = ir("object-body", &source()) else {
        return;
    };
    for name in HOT {
        let body = body(&text, name);
        assert!(
            !body.is_empty(),
            "`{name}` в IR рантайма не нашлась: свидетель считал бы пустоту"
        );
        let atomics = atomics(&body);
        assert!(
            atomics.is_empty(),
            "у `{name}` атомарная операция осталась в теле: {}.\n\
             Тело точки входа инлайнится в горячий виток, и с атомарной \
             операцией внутри инлайнер перестаёт делить его на половины - \
             колонному ядру это стоило 1.64 раза. Унеси её в отдельную \
             `ADAMAS_SHARED_HALF`-функцию, а потом **перемерь строку 4а** \
             `docs/measurements/workload-gap/`.",
            atomics.join("; ")
        );
    }
}

/// Ветвь по флагу при этом на месте: половина вынесена, а не выброшена.
///
/// Без этой половины свидетель зеленел бы и на рантайме, у которого
/// атомарности нет вовсе, - то есть охранял бы скорость ценой корректности.
#[test]
fn the_flag_branch_is_moved_and_not_dropped() {
    let Some(text) = ir("object-halves", &source()) else {
        return;
    };
    for (entry, half) in PAIRS {
        let called = body(&text, entry)
            .iter()
            .filter(|line| line.contains(&format!("@{half}(")))
            .count();
        assert_eq!(
            called, 1,
            "`{entry}` зовёт разделяемую половину `{half}` {called} раз, а не один"
        );
    }
    for half in HALVES {
        assert!(
            !atomics(&body(&text, half)).is_empty(),
            "у `{half}` не осталось атомарной операции: гибридный режим потерял \
             разделяемую половину"
        );
        assert!(
            noinline(&text, half),
            "`{half}` не помечена `noinline`: «вынесена» она тогда только на \
             словах, и инлайнер вернёт её в тело"
        );
    }
}

/// Свидетель различает, и предъявлено это правкой, а не доводом.
///
/// Верни атомарную операцию в тело - ровно так, как она стояла у трека I, - и
/// счёт обязан перестать быть нулём. Свидетель, переживающий возврат
/// регрессии, проверял бы не то.
#[test]
fn the_witness_falls_when_the_atomic_returns() {
    let put_back = source().replace(
        "        return adamas_unique_shared(header);",
        "        return __atomic_load_n(&header->rc, __ATOMIC_ACQUIRE) == 0;",
    );
    assert!(
        put_back != source(),
        "мутант не встал: текст `adamas_is_unique` разошёлся с тем, что ищет \
         подстановка"
    );
    let Some(text) = ir("object-mutant", &put_back) else {
        return;
    };
    let found = atomics(&body(&text, "adamas_is_unique"));
    assert!(
        !found.is_empty(),
        "атомарная операция вернулась в тело `adamas_is_unique`, а свидетель её \
         не увидел: он не о том"
    );
    eprintln!(
        "свидетель/гибридный режим: возврат ветви виден как {}",
        found.join("; ")
    );
}

/// Текст `object.c` как он лежит в рантайме.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn source() -> String {
    let path = Path::new(env!("ADAMAS_RUNTIME_SOURCES")).join("object.c");
    std::fs::read_to_string(&path).unwrap()
}

/// IR данного текста `object.c`, собранного той же строкой, что и замер.
///
/// `None` значит «LLVM объявлен отсутствующим»: правило одно на всех
/// свидетелей и записано в [`harness::llvm_toolchains`].
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn ir(stem: &str, text: &str) -> Option<String> {
    harness::llvm_toolchains()?;
    let clang = std::env::var_os(harness::CLANG_VARIABLE)
        .filter(|it| !it.is_empty())
        .unwrap_or_else(|| {
            panic!(
                "`{}` не задан, а в dev-shell он есть: IR рантайма собрать нечем",
                harness::CLANG_VARIABLE
            )
        });
    let dir = harness::scratch();
    let source: PathBuf = dir.join(format!("{stem}.c"));
    let shown = dir.join(format!("{stem}.ll"));
    std::fs::write(&source, text).unwrap();
    // `-O2`, а не `-O1`: свидетель охраняет число, снятое на `-O2 -flto`, и
    // решение инлайнера на другом уровне оптимизации было бы другим.
    let made = Command::new(&clang)
        .args(["-std=c11", "-O2", "-S", "-emit-llvm", "-w"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source)
        .arg("-o")
        .arg(&shown)
        .output()
        .unwrap();
    assert!(
        made.status.success(),
        "`{stem}.c` не собрался в IR:\n{}",
        String::from_utf8_lossy(&made.stderr)
    );
    Some(std::fs::read_to_string(&shown).unwrap())
}

/// Строки тела названной функции - от её `define` до закрывающей скобки.
fn body(text: &str, name: &str) -> Vec<String> {
    let head = format!("@{name}(");
    let mut within = false;
    let mut out = Vec::new();
    for line in text.lines() {
        if line.starts_with("define") {
            within = line.contains(&head);
            continue;
        }
        if line == "}" {
            within = false;
            continue;
        }
        if within {
            out.push(line.trim().to_owned());
        }
    }
    out
}

/// Атомарные операции в наборе строк IR - целиком, чтобы их было видно в отказе.
fn atomics(body: &[String]) -> Vec<String> {
    body.iter()
        .filter(|line| {
            line.contains("atomicrmw ")
                || line.contains("cmpxchg ")
                || line.contains("fence ")
                || line.contains(" atomic ")
        })
        .cloned()
        .collect()
}

/// Помечена ли функция `noinline` - по её группе атрибутов, а не по комментарию.
fn noinline(text: &str, name: &str) -> bool {
    let head = format!("@{name}(");
    let Some(define) = text
        .lines()
        .find(|line| line.starts_with("define") && line.contains(&head))
    else {
        return false;
    };
    let Some(group) = define
        .split_whitespace()
        .find(|word| word.starts_with('#'))
        .map(str::to_owned)
    else {
        return false;
    };
    text.lines()
        .find(|line| line.starts_with(&format!("attributes {group} =")))
        .is_some_and(|line| line.contains("noinline"))
}
