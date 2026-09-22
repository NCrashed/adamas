//! Названный отказ на исчерпание стека - и молчание там, где он не к месту.
//!
//! Правило живёт в `c/stack.c` и звано `main.c` первой строкой. Утверждений о
//! нём ровно два, и порознь ни одно из них не значит ничего.
//!
//! *Исчерпанный стек называет себя.* Без этой половины правило можно было бы
//! снять целиком, и никто бы не заметил: программа падала бы, как падала.
//!
//! *Обращение мимо стека остаётся сигналом.* Без этой половины правило
//! выродилось бы в «всякий SIGSEGV есть исчерпание стека» - то есть в ложное
//! свидетельство, которое хуже молчания: дефект памяти назвался бы чужим
//! именем и увёл бы поиск. Мутант, снимающий проверку границ в обработчике,
//! красит ровно эту половину.
//!
//! Стенды - C, а не Adamas, и это вынужденно: дикого указателя в языке нет, а
//! глубина, нужная первому стенду, зависела бы от того, сколько кадров строит
//! понижение. Здесь оба стенда меряют рантайм и только его.

#![cfg(unix)]

use std::os::unix::process::ExitStatusExt as _;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Код, которым уходит названный отказ (`ADAMAS_STACK_EXIT` в `c/stack.c`).
const REFUSED: i32 = 3;

/// Начало названного отказа. Совпадение с текстом рантайма - часть свидетеля.
const NAMED: &str = "стек исчерпан";

/// Рекурсия с крупным кадром: стек кончится при любом `ulimit`.
const DEEP: &str = r#"
#include "adamas.h"
#include <stdio.h>

/* Кадр в четыре килобайта, и он `volatile`: иначе компилятор снимет и его, и
 * рекурсию. Возврат складывается с прочитанным, поэтому хвостовым вызов не
 * становится ни при каком уровне. */
static unsigned long long deep(unsigned long long n) {
    volatile char pad[4096];
    pad[0] = (char)(n & 0x7f);
    if (n == 0) {
        return (unsigned long long)pad[0];
    }
    return deep(n - 1) + (unsigned long long)pad[0];
}

int main(void) {
    adamas_stack_guard();
    printf("%llu\n", deep(100000000ull));
    return 0;
}
"#;

/// Обращение по адресу, до стека не дотягивающему.
const WILD: &str = r#"
#include "adamas.h"
#include <stdio.h>

int main(void) {
    volatile int *wild = (volatile int *)0x10;
    adamas_stack_guard();
    *wild = 1;
    printf("обращение прошло: страница нулевого адреса отображена\n");
    return 0;
}
"#;

/// Чем кончился прогон стенда.
struct Ran {
    /// Код возврата; `None` - процесс убит сигналом.
    code: Option<i32>,
    /// Сигнал, которым убит; `None` - вышел сам.
    signal: Option<i32>,
    /// Что ушло в stderr.
    printed: String,
}

/// Собирает стенд тем же компилятором и с тем же рантаймом, что и корпус.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn ran(name: &str, source: &str) -> Ran {
    let dir = PathBuf::from(env!("OUT_DIR")).join("stack");
    std::fs::create_dir_all(&dir).expect("каталог стенда обязан заводиться");
    let file = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&file, source).expect("стенд обязан записываться");
    let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
    let compiled = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O1"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&file)
        .args(
            env!("ADAMAS_RUNTIME_UNITS")
                .split(',')
                .map(|unit| sources.join(unit)),
        )
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("компилятор обязан запускаться");
    assert!(
        compiled.status.success(),
        "стенд `{name}` не собрался:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let run = Command::new(&binary)
        .output()
        .expect("стенд обязан пускаться");
    Ran {
        code: run.status.code(),
        signal: run.status.signal(),
        printed: String::from_utf8_lossy(&run.stderr).into_owned(),
    }
}

/// Исчерпанный стек называет причину и уходит своим кодом.
#[test]
fn an_exhausted_stack_refuses_by_name() {
    let run = ran("deep", DEEP);
    assert!(
        run.printed.contains(NAMED),
        "исчерпание стека не назвало себя: {} (сигнал {:?}, код {:?})",
        run.printed,
        run.signal,
        run.code
    );
    assert_eq!(
        run.code,
        Some(REFUSED),
        "отказ ушёл не своим кодом (сигнал {:?})",
        run.signal
    );
}

/// Обращение мимо стека остаётся сигналом и чужим именем не называется.
#[test]
fn a_fault_away_from_the_stack_is_left_alone() {
    let run = ran("wild", WILD);
    assert!(
        !run.printed.contains(NAMED),
        "дефект памяти назвался исчерпанием стека: правило свидетельствует ложно"
    );
    assert!(
        run.signal.is_some(),
        "обращение по адресу 0x10 не уронило процесс: код {:?}, вывод {}",
        run.code,
        run.printed
    );
}
