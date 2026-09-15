//! `ThreadSanitizer` над счётчиком разделяемого значения (§5.1).
//!
//! # Зачем инструмент, если рядом уже есть стенд
//!
//! `tests/atomic.rs` ловит **случившуюся** гонку: пропавшую инкрементацию видно
//! числом. Планировщик, однако, вправе развести потоки так, что перекрытия не
//! будет вовсе, и тогда тот стенд зеленеет на сломанном коде. Санитайзер ловит
//! саму **возможность**: несинхронизированную пару доступов он назовёт и там,
//! где число сошлось.
//!
//! # Чем стенд держится честным
//!
//! Проверку проверяют мутантом, как всякую другую: рядом с честным прогоном
//! стоит **ломаный**, который считает счётчик голым `header->rc += 1` в обход
//! рантайма. Заголовок объекта в `adamas.h` открыт, поэтому написать такое
//! можно прямо в стенде, не трогая рантайм. Санитайзер обязан назвать гонку у
//! ломаного и промолчать у честного; промолчи он у обоих - инструмент не
//! включился, и тест это скажет, а не пройдёт.
//!
//! *Что проверка напечатает, если сломать проверяемое.* Сними `lock` с
//! инкрементации рантайма - и честный прогон начнёт печатать `data race` на
//! `adamas_dup`. Именно эта строка и есть наблюдаемое.
//!
//! # Границы
//!
//! Санитайзер не ловит того, чего программа не сделала: он видит **исполненные**
//! пары доступов. Стенд поэтому гоняет тот же ряд операций, что гонял бы
//! `spawn`, - взятие, отдачу и вопрос об уникальности, - на одном разделяемом
//! объекте из нескольких потоков.
//!
//! Собирается стенд `ADAMAS_CC`; если он не умеет `-fsanitize=thread`, тест
//! говорит об этом и не проверяет ничего. Молчаливого пропуска нет.

#![allow(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

/// Общая шапка стенда: объект, потоки, ход.
const HARNESS: &str = r#"
#include "adamas.h"
#include <pthread.h>
#include <stdio.h>

#define THREADS 4
#define ROUNDS 20000

static adamas_value target;

static void *walk(void *arg) {
    (void)arg;
    for (int round = 0; round < ROUNDS; round += 1) {
        TAKE;
        GIVE;
    }
    return NULL;
}

int main(void) {
    pthread_t threads[THREADS];
    target = adamas_alloc(0, 1);
    adamas_set_field(target, 0, adamas_imm(1));
    MARK;
    for (int at = 0; at < THREADS; at += 1) {
        pthread_create(&threads[at], NULL, walk, NULL);
    }
    for (int at = 0; at < THREADS; at += 1) {
        pthread_join(threads[at], NULL);
    }
    printf("rc=%u unique=%d\n", adamas_rc(target), adamas_is_unique(target));
    adamas_drop(target, NULL);
    printf("live=%zu\n", adamas_stat_live_everywhere());
    return 0;
}
"#;

/// Честный стенд: счётчик трогает только рантайм, объект помечен разделяемым.
fn honest() -> String {
    HARNESS
        .replace("MARK;", "adamas_share(target);")
        .replace("TAKE;", "adamas_dup(target);")
        .replace("GIVE;", "adamas_drop(target, NULL);")
}

/// Ломаный: тот же ряд операций голым счётчиком, мимо рантайма.
///
/// Это и есть «неатомарный RC» дословно - то, чем счётчик был до этого трека.
/// Пометки нет: она ничего бы не меняла, счётчик правится в обход.
fn broken() -> String {
    HARNESS
        .replace("MARK;", "(void)0;")
        .replace("TAKE;", "adamas_header_of(target)->rc += 1;")
        .replace("GIVE;", "adamas_header_of(target)->rc -= 1;")
}

/// Что сказал прогон под санитайзером.
struct Watched {
    /// Собрался ли стенд вовсе.
    built: bool,
    /// Назвал ли санитайзер гонку.
    raced: bool,
    /// Что стенд напечатал.
    printed: String,
}

/// Каталог под стенды. Свой у этого теста: прогоны идут параллельно.
fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join("race");
    let _ = std::fs::create_dir_all(&dir);
    dir
}

/// Собирает стенд с санитайзером и гоняет его.
///
/// # Panics
///
/// Не записался стенд, не запустился компилятор либо собранный бинарь: это
/// сломанное окружение, а не наблюдение.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn watched(stem: &str, text: &str) -> Watched {
    let dir = scratch();
    let source = dir.join(format!("{stem}.c"));
    let binary = dir.join(stem);
    std::fs::write(&source, text).expect("стенд обязан записываться");

    // Рантайм пересобирается **санитайзером** вместе со стендом, а не берётся
    // готовым: TSan видит только то, что инструментировано, и счётчик, собранный
    // без него, оказался бы для него невидим. Ровно тот жанр обманчивого
    // свидетеля, от которого стенд и заводится.
    let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
    let compiled = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O1", "-g", "-fsanitize=thread", "-pthread"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source)
        .args(
            env!("ADAMAS_RUNTIME_UNITS")
                .split(',')
                .map(|unit| sources.join(unit)),
        )
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("компилятор обязан запускаться");
    if !compiled.status.success() {
        return Watched {
            built: false,
            raced: false,
            printed: String::from_utf8_lossy(&compiled.stderr).into_owned(),
        };
    }

    let ran = Command::new(&binary)
        .output()
        .expect("стенд обязан запускаться");
    let complained = String::from_utf8_lossy(&ran.stderr).into_owned();
    Watched {
        built: true,
        raced: complained.contains("data race"),
        printed: String::from_utf8_lossy(&ran.stdout).trim_end().to_owned(),
    }
}

/// Санитайзер молчит на рантайме и кричит на голом счётчике.
///
/// Обе половины обязательны. Без первой утверждение «атомарно» держалось бы на
/// том, что инструмент вообще не запустился; без второй - на том, что он ничего
/// не умеет ловить.
#[test]
fn the_sanitizer_names_the_race_the_runtime_does_not_have() {
    let broken = watched("broken", &broken());
    if !broken.built {
        // Не «пропустить молча»: сказать и остановиться. Отсутствие
        // санитайзера - факт окружения, и читать его должен человек.
        eprintln!(
            "ThreadSanitizer недоступен у `ADAMAS_CC`, договор §5.1 этим прогоном не проверялся:\n{}",
            broken.printed
        );
        return;
    }
    assert!(
        broken.raced,
        "санитайзер не назвал гонку там, где счётчик правится голым `+=`: \
         инструмент не ловит ничего, и молчание на честном стенде ничего не значит"
    );

    let honest = watched("honest", &honest());
    assert!(
        honest.built,
        "честный стенд не собрался:\n{}",
        honest.printed
    );
    assert!(
        !honest.raced,
        "санитайзер назвал гонку на счётчике рантайма: атомарности нет"
    );
    // Ряд взятий и отдач сбалансирован, значит объект обязан вернуться к
    // уникальности, а после последнего дропа - не остаться живым.
    assert_eq!(
        honest.printed, "rc=0 unique=1\nlive=0",
        "честный стенд посчитал не то"
    );
    eprintln!(
        "санитайзер: ломаный стенд - гонка, честный - тишина, {}",
        honest.printed.replace('\n', ", ")
    );
}
