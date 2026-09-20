//! Свёртка чужого вызова: почему она корректность, а не оптимизация (§5.3).
//!
//! Компилятор вправе узнать чужой символ **по имени** и посчитать его сам,
//! когда аргумент константа. Считает он при этом не обязательно то же, что
//! библиотека: `cbrt(27.0)` `gcc` сворачивает в `3.0` (`4008000000000000`) уже
//! на `-O0`, а glibc в прогоне отвечает `3.0000000000000004`
//! (`4008000000000001`) - корректно округлённый кубический корень и есть
//! тройка, а библиотека промахивается на один ULP. Расходятся из-за этого не мы
//! с библиотекой, а **два наших понижения**, потому что машина и LLVM отвечают
//! как glibc. То есть §5.3 обещает вызов, а получает иногда число.
//!
//! # Два запрета, и сегодня срабатывает один
//!
//! У C-стороны их два, и это измерено, а не задумано.
//!
//! 1. **Своё имя у символа.** `emit_c::prototypes` объявляет не `cbrt`, а
//!    `adamas_foreign_cbrt` с ассемблерной меткой - заведено это против другой
//!    беды (`extern uint64_t malloc(uint64_t)` рядом с `<stdlib.h>` есть
//!    «conflicting types»), но свёртку оно отменяет заодно: узнавание у `gcc`
//!    идёт по написанному имени, и `adamas_foreign_cbrt` он не узнаёт. Измерено
//!    прямо: то же тело под именем `cbrt` сворачивается на `-O1`, под
//!    переименованным - не сворачивается даже на `-O2`.
//! 2. **`-fno-builtin`** в ключах сборки (`native.rs`, `PROGRAM_FLAGS`).
//!    Сегодня его вклад **ноль**: до него дело не доходит, первый запрет
//!    срабатывает раньше. Держится он не числом, а тем, что переживёт смену
//!    схемы именования, и тем, что симметричен `nobuiltin` у `.ll`, - там
//!    запрет как раз наблюдаем.
//!
//! У `.ll` запрет один - атрибут `nobuiltin` у объявления, - и он **работает**:
//! без него `opt -O2` считает `pow(2.0, 10.0)` и `labs(-7)` на месте, и вызовов
//! в объектнике не остаётся. Ответ при этом не меняется (LLVM сворачивает libm
//! хостовой libm, то есть той же, которую зовёт машина), поэтому наблюдается он
//! счётом вызовов, а не числом.
//!
//! # Мутанты
//!
//! Сняты на каждой правке порознь, с возвратом между ними. Счёт - упавших
//! тестов набора `adamas-codegen --test folding --test agreement --test
//! foreign_call`, `adamas-interp --test running`, `adamas-cli --test linking
//! --test golden`; контроль на чистом дереве - ноль. Полная таблица -
//! `docs/phase8-trackD-notes.md`.
//!
//! | Мутант | Красных |
//! |---|---|
//! | `emit_c::local`: отдавать символ как есть, без переименования | 2 |
//! | `emit_llvm::foreigns`: снять `nobuiltin` у объявления | 1 |
//! | `native.rs`: снять `-fno-builtin` из `PROGRAM_FLAGS` | **0** |
//! | `harness`: снять `-fno-builtin` из ключей сборки | **0** |

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

mod harness;

use std::path::Path;
use std::process::Command;

use adamas_codegen::llvm::Pipeline;

/// Программа корпуса, а не строка здесь: вторая копия разъехалась бы молча.
fn source() -> String {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval/extern-c.adamas");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|why| panic!("фикстуры {} нет: {why}", path.display()))
}

/// Ответ, который даёт **библиотека**: `cbrt(27.0)` в glibc промахивается на
/// один ULP, и свёрнутый ответ от него отличим.
const FROM_THE_LIBRARY: &str = "3.0000000000000004";

/// Порождённый C зовёт чужой символ и отвечает то же, что библиотека.
///
/// Красен от снятия переименования дважды: без него фикстура не собирается
/// вовсе (`malloc` спорит с `<stdlib.h>`), а собравшись - считала бы `cbrt`
/// сама. Оба исхода приезжают сюда паникой заготовки либо расхождением ответа.
///
/// Второй половиной - сборка с `-fbuiltin`, то есть **без** запрета ключом.
/// Ответ у неё тот же, и это не слабость свидетеля, а замер: сворачивать
/// `gcc` нечего, имя ему незнакомо.
#[test]
fn the_c_lowering_answers_what_the_library_answers() {
    let source = source();
    let expected = harness::printed(&source);
    assert!(
        expected.contains(FROM_THE_LIBRARY),
        "машина обязана отвечать ответом библиотеки: {expected}"
    );

    let text = harness::text(&source).expect("понижение обязано взять чужой вызов");
    assert!(
        text.contains("adamas_foreign_cbrt(") && !text.contains("= cbrt("),
        "чужой символ обязан зваться своим именем с меткой, а не написанным"
    );

    let (standard, _) = harness::built_with("folding-standard", &text, &[]);
    assert_eq!(
        standard.trim_end(),
        expected,
        "штатная сборка разошлась с машиной"
    );

    // `-fbuiltin` идёт **после** штатных ключей и потому побеждает.
    let (permitted, _) = harness::built_with("folding-permitted", &text, &["-fbuiltin"]);
    assert_eq!(
        permitted.trim_end(),
        expected,
        "сборка без запрета ключом разошлась с машиной: переименование перестало держать"
    );
}

/// `gcc` сворачивает чужой вызов, когда символ объявлен **своим** именем.
///
/// Свидетель не о нас, а о компиляторе: без него оба запрета выше выглядели бы
/// осторожностью. Написан диалектом эмиттера - то же объявление, тот же вызов,
/// тот же уровень оптимизации, - и различает две сборки **битами**, а не
/// печатью: у C и у машины форматы плавающего разные по построению.
#[test]
fn a_symbol_declared_under_its_own_name_is_folded_by_the_c_compiler() {
    assert_eq!(
        probe_bits("extern double cbrt(double);", "cbrt", &[]),
        0x4008_0000_0000_0000,
        "свёртка перестала случаться: запреты держат уже не эту беду"
    );
    assert_eq!(
        probe_bits("extern double cbrt(double);", "cbrt", &["-fno-builtin"]),
        0x4008_0000_0000_0001,
        "с запретом ключом обязан зваться настоящий `cbrt` из libm"
    );
}

/// Тот же вызов под переименованным именем: свёртки нет и без ключа.
///
/// Это и есть замер, из-за которого вклад `-fno-builtin` сегодня равен нулю.
/// Уровень оптимизации взят выше штатного нарочно: «не сворачивает на `-O1`»
/// было бы утверждением про уровень, а не про имя.
#[test]
fn a_renamed_symbol_is_not_folded_even_with_builtins_allowed() {
    assert_eq!(
        probe_bits(
            "extern double adamas_foreign_cbrt(double) __asm__(\"cbrt\");",
            "adamas_foreign_cbrt",
            &["-O2"]
        ),
        0x4008_0000_0000_0001,
        "переименованный символ свернули: узнавание идёт не по имени?"
    );
}

/// Биты ответа `cbrt(27.0)` у программы с названным объявлением и ключами.
///
/// Диалект эмиттера, а не эмиттер: свидетель спрашивает про **компилятор C**,
/// и написанная руками единица трансляции здесь честнее порождённой - в ней
/// видно ровно то, о чём вопрос. Сверяются биты, а не печать: у C и у машины
/// форматы плавающего разные по построению.
fn probe_bits(declaration: &str, call: &str, flags: &[&str]) -> u64 {
    // Имя своё у каждой сборки: тесты крейта идут параллельно, а файл один.
    static COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let at = COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let source = format!(
        "#include <stdint.h>\n\
         #include <stdio.h>\n\
         #include <string.h>\n\
         {declaration}\n\
         int main(void) {{\n\
         \x20   double v = {call}(27.0);\n\
         \x20   uint64_t bits;\n\
         \x20   memcpy(&bits, &v, sizeof bits);\n\
         \x20   printf(\"%016llx\\n\", (unsigned long long)bits);\n\
         \x20   return 0;\n\
         }}\n"
    );
    let printed = built_and_run(&format!("folding-probe-{at}"), &source, flags);
    u64::from_str_radix(printed.trim(), 16).unwrap_or_else(|why| panic!("{printed:?}: {why}"))
}

/// Самостоятельная единица C: собрать названными ключами, запустить, отдать
/// stdout.
///
/// Ни рантайма, ни порождённого кода: вопрос здесь про **компилятор**, и мерить
/// его порождённым текстом значило бы мерить заодно всё остальное. `-lm` тот
/// же, что у штатной сборки.
fn built_and_run(stem: &str, source: &str, flags: &[&str]) -> String {
    let dir = harness::scratch();
    let path = dir.join(format!("{stem}.c"));
    let binary = dir.join(stem);
    std::fs::write(&path, source).unwrap();
    let compiled = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O1", "-Wall"])
        .args(flags)
        .arg(&path)
        .arg("-lm")
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{stem}: единица не собралась:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let run = Command::new(&binary).output().unwrap();
    assert!(
        run.status.success(),
        "{stem}: прогон оборвался:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8(run.stdout).unwrap()
}

/// Дизассемблированный объектник целиком.
///
/// Свёрнутый чужой вызов исчезает из кода, не меняя ответа, и прочитать это
/// можно только здесь.
fn disassembled(tools: &adamas_codegen::llvm::Toolchain, object: &Path) -> String {
    let shown = Command::new(tools.tool("llvm-objdump"))
        .arg("-dr")
        .arg(object)
        .output()
        .unwrap();
    assert!(
        shown.status.success(),
        "`{}` не дизассемблировался",
        object.display()
    );
    String::from_utf8_lossy(&shown.stdout).into_owned()
}

/// Объявление `.ll` запрещает свёртку, и запрет наблюдаем **счётом вызовов**.
///
/// Ответом его не поймать: LLVM сворачивает libm хостовой libm, то есть той же,
/// которую зовёт машина, и числа сходятся. Наблюдается поэтому другое - что
/// вызов **есть**: без атрибута `pow` и `labs` с константными аргументами
/// исчезают из объектника вовсе, а §5.3 обещает вызов, а не равное ему число.
#[test]
fn the_llvm_declaration_refuses_folding() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts =
        harness::llvm_text("folding-llvm", &source()).expect("понижение обязано взять фикстуру");
    assert!(
        artefacts.ll.contains("declare i64 @labs(i64) nobuiltin"),
        "объявление чужого символа обязано нести запрет свёртки"
    );
    let object = harness::llvm_object("folding-llvm", &artefacts, &tools, &Pipeline::optimised());
    let disassembled = disassembled(&tools, &object);
    for symbol in ["cbrt", "pow", "labs"] {
        assert!(
            disassembled.contains(symbol),
            "{symbol} свёрнут оптимизатором: вызова в объектнике нет"
        );
    }
}
