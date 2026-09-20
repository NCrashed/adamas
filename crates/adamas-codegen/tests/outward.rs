//! Сходятся ли три вычислителя на чужом вызове (§5.3, §10 вопрос 182).
//!
//! Договор корпуса (`agreement.rs`) держит инвариант: каждая программа либо
//! сходится у всех трёх, либо стоит в `LANGUAGE` с названной причиной. Вопрос
//! 182 спрашивает, что с этим делать, когда программа зовёт сишную функцию.
//! Трек C волны 1 Фазы 8 отвечает на него замером, и здесь - его вторая
//! половина: сама сверка.
//!
//! # Что здесь за программа
//!
//! `cbrt 27.0` - один чужой вызов и ничего сверх. Три стороны:
//!
//! - **машина** зовёт `cbrt` из `libm.so.6` через `dlopen`/`dlsym`
//!   (`adamas-interp`, `src/foreign.rs`);
//! - **C** зовёт его напрямую, как позвал бы порождённый текст;
//! - **текстовый `.ll`** объявляет `declare double @cbrt(double)` и зовёт.
//!
//! Обе понижающие стороны написаны **диалектом эмиттеров**, а не эмиттерами:
//! узла IR под внешний вызов сегодня нет вовсе, и заводит его трек B. Довод и
//! граница те же, что у стенда трека A (`tests/foreign.rs`, «Граница
//! доказанного названа»): доказано «форма лежит в подмножестве, которое
//! эмиттеры печатают, и работает», а не «эмиттер её печатает».
//!
//! Сверяются **биты** ответа, а не его печать. Печать плавающего у C и у машины
//! разная по построению (`%.17g` против кратчайшего обратимого), и сверка
//! текстов мерила бы форматирование.
//!
//! # Главная находка стоит здесь, а не в отчёте
//!
//! Сишный компилятор **сворачивает** чужой вызов с литеральным аргументом сам,
//! и сворачивает **иначе**, чем библиотека: `gcc` даёт `cbrt(27.0) = 3.0`
//! (корректно округлённое), glibc в прогоне - `3.0000000000000004`. LLVM на том
//! же месте не сворачивает ничего. То есть на программе с литеральным
//! аргументом три вычислителя расходятся, и расходятся **не** из-за машины:
//! между собой расходятся два понижения.
//!
//! Свидетели предъявляют это прогоном ([`the_c_compiler_folds_the_foreign_call`],
//! [`the_llvm_pipeline_does_not_fold_the_foreign_call`],
//! [`no_builtin_makes_the_c_side_agree_again`]) и называют лекарство:
//! `-fno-builtin`. Поэтому сверка трёх идёт на **непрозрачном** аргументе -
//! настоящая чужая функция аргумента времени компиляции обычно и не имеет.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;
use std::sync::OnceLock;

use adamas_codegen::llvm::{Pipeline, Toolchain};
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::prim::{Prim, PrimTy};
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Binder, Term};
use adamas_core::value::Env;
use adamas_interp::{Foreign, Machine};

/// Библиотека: glibc держит её отдельным файлом, и `cbrt` есть только в ней.
const LIBRARY: &str = "libm.so.6";
/// Символ: `double cbrt(double)`.
const SYMBOL: &str = "cbrt";
/// Аргумент: куб, на котором glibc **не** точен, - расхождение наблюдаемо.
const INPUT: f64 = 27.0;

/// Спутник: непрозрачный источник аргумента и печать битов ответа.
///
/// Непрозрачным аргумент делает **отдельная единица трансляции** без
/// межмодульной оптимизации, и только она: мутант «снять `volatile`» не уронил
/// ни одного свидетеля. Ключевое слово оставлено как страховка на случай, когда
/// спутник вздумают собрать вместе с программой, а не как то, чем непрозрачность
/// держится сегодня.
const COMPANION: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static volatile double held = 27.0;

double adamas_outward_input(void) { return held; }

void adamas_outward_print(double value) {
    uint64_t bits;
    memcpy(&bits, &value, sizeof bits);
    printf("%016llx\n", (unsigned long long)bits);
}
"#;

/// Понижение в C, как его написал бы эмиттер: аргумент приходит извне.
const IN_C: &str = r"
double cbrt(double);
double adamas_outward_input(void);
void adamas_outward_print(double);

int main(void) {
    adamas_outward_print(cbrt(adamas_outward_input()));
    return 0;
}
";

/// То же с литеральным аргументом: место, где компилятор волен свернуть.
const IN_C_LITERAL: &str = r"
double cbrt(double);
void adamas_outward_print(double);

int main(void) {
    adamas_outward_print(cbrt(27.0));
    return 0;
}
";

/// Понижение в текстовый `.ll`: `declare` плюс `call`, и ничего сверх.
const IN_LLVM: &str = r"
declare double @cbrt(double)
declare double @adamas_outward_input()
declare void @adamas_outward_print(double)

define i32 @main() {
entry:
  %x = call double @adamas_outward_input()
  %y = call double @cbrt(double %x)
  call void @adamas_outward_print(double %y)
  ret i32 0
}
";

/// То же с литеральным аргументом.
const IN_LLVM_LITERAL: &str = r"
declare double @cbrt(double)
declare void @adamas_outward_print(double)

define i32 @main() {
entry:
  %y = call double @cbrt(double 2.700000e+01)
  call void @adamas_outward_print(double %y)
  ret i32 0
}
";

/// Место под объектники и бинари этого свидетеля.
fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join("outward");
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Зовёт компилятор и роняет прогон его же выводом.
fn run(command: &mut Command, what: &str) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{what}: не собралось\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Спутник объектником: собирается однажды на весь прогон.
///
/// Однажды не ради скорости: свидетели крейта идут потоками одного процесса, и
/// пересборка одного и того же файла дала бы «Text file busy» на чужом прогоне
/// (жанр пойман треком A, `tests/foreign.rs`).
fn companion() -> &'static Path {
    static IT: OnceLock<PathBuf> = OnceLock::new();
    IT.get_or_init(|| {
        let dir = scratch();
        let source = dir.join("companion.c");
        let object = dir.join("companion.o");
        std::fs::write(&source, COMPANION).unwrap();
        run(
            Command::new(env!("ADAMAS_CC"))
                .args(["-std=c11", "-O2", "-Wall", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&object),
            "спутник",
        );
        object
    })
}

/// Собирает C-сторону названными ключами и отдаёт напечатанные биты.
fn in_c(stem: &str, text: &str, extra: &[&str]) -> u64 {
    let dir = scratch();
    let source = dir.join(format!("{stem}.c"));
    let binary = dir.join(stem);
    std::fs::write(&source, text).unwrap();
    run(
        Command::new(env!("ADAMAS_CC"))
            .args(["-std=c11", "-O2", "-ffp-contract=off", "-Wall"])
            .args(extra)
            .arg(&source)
            .arg(companion())
            .arg("-lm")
            .arg("-o")
            .arg(&binary),
        stem,
    );
    printed(&binary)
}

/// Собирает `.ll`-сторону тем же конвейером, каким её собирал бы эмиттер.
fn in_llvm(tools: &Toolchain, stem: &str, text: &str) -> u64 {
    let dir = scratch();
    let source = dir.join(format!("{stem}.ll"));
    std::fs::write(&source, text).unwrap();
    let object = Pipeline::optimised()
        .run(tools, &source, stem)
        .unwrap_or_else(|error| panic!("{stem}: конвейер LLVM отказал: {error}"));
    let binary = dir.join(format!("{stem}.bin"));
    run(
        Command::new(env!("ADAMAS_CC"))
            .arg(&object)
            .arg(companion())
            .arg("-lm")
            .arg("-o")
            .arg(&binary),
        stem,
    );
    printed(&binary)
}

/// Прогон бинаря: биты ответа шестнадцатеричной строкой со stdout.
fn printed(binary: &Path) -> u64 {
    let output = Command::new(binary).output().unwrap();
    assert!(
        output.status.success(),
        "{}: прогон оборвался: {}",
        binary.display(),
        output.status
    );
    let text = String::from_utf8(output.stdout).unwrap();
    u64::from_str_radix(text.trim(), 16)
        .unwrap_or_else(|_| panic!("{}: ответ не биты: `{}`", binary.display(), text.trim()))
}

/// Ответ машины: те же биты, но из `adamas eval`.
///
/// Постулат, а не определение: тело развернулось бы δ-шагом раньше, чем машина
/// дошла бы до внешнего вызова. Слова `extern` в языке нет - объявление
/// приходит машине мимо поверхности, и заводит его трек B, не этот.
fn by_machine() -> u64 {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(
            &mut metas,
            SYMBOL,
            Mult::Many,
            0,
            Term::Pi(
                Binder::explicit(Mult::Many),
                "x".into(),
                Rc::new(Term::Prim(Prim::Ty(PrimTy::Float64))),
                Row::empty(),
                Rc::new(Term::Prim(Prim::Ty(PrimTy::Float64))),
            ),
        )
        .expect("постулат обязан объявляться");
    let term =
        Term::constant(SYMBOL).apply([Term::Prim(Prim::literal(PrimTy::Float64, INPUT.to_bits()))]);

    let mut machine = Machine::new(&signature);
    machine.declare_foreign(
        SYMBOL,
        Foreign::new(LIBRARY, SYMBOL, &[PrimTy::Float64], PrimTy::Float64),
    );
    let value = machine
        .evaluate(&Env::default(), &term)
        .expect("машина обязана сходить наружу");
    match machine.read(value).expect("ответ обязан читаться") {
        Term::Prim(Prim::Lit(PrimTy::Float64, bits)) => bits,
        other => panic!("ответ не литерал `Float64`: {}", other.printed(None)),
    }
}

/// Цепочка LLVM либо объявленное её отсутствие.
///
/// Правило то же, что у прочих свидетелей понижения: инструмента нет - прогон
/// падает, а не молчит.
fn toolchain() -> Option<Toolchain> {
    if std::env::var("ADAMAS_LLVM").is_ok_and(|it| it == "absent") {
        eprintln!("LLVM объявлен отсутствующим (ADAMAS_LLVM=absent): сверка трёх не полна");
        return None;
    }
    Some(Toolchain::from_variable(
        adamas_codegen::llvm::TOOLS_VARIABLE,
    ))
}

/// Три вычислителя на чужом вызове отвечают **одно**.
///
/// Это и есть ответ трека C на вопрос «а сходятся ли три»: сходятся, и договор
/// корпуса вариант (а) не рвёт. Аргумент непрозрачен намеренно - с литеральным
/// не сходятся, и почему, показывают соседние свидетели.
#[test]
fn all_three_evaluators_answer_the_same_bits() {
    let machine = by_machine();
    let c = in_c("outward-c", IN_C, &[]);
    assert_eq!(c, machine, "C-понижение ответило не то, что машина");
    let Some(tools) = toolchain() else {
        return;
    };
    let llvm = in_llvm(&tools, "outward-ll", IN_LLVM);
    assert_eq!(llvm, machine, "LLVM-понижение ответило не то, что машина");
}

/// Сишный компилятор сворачивает чужой вызов сам - и считает **иначе**.
///
/// Измеренная находка трека, предъявленная прогоном. `gcc` подставляет
/// корректно округлённый `cbrt(27.0) = 3.0` (и делает это уже на `-O0`), а
/// glibc в прогоне отвечает `3.0000000000000004`. Разница - один ULP, и
/// наблюдаема она любой программой корпуса, у которой аргумент чужого вызова
/// известен на сборке.
///
/// Свидетель предъявляет расхождение, а не оговаривает его: перестань
/// компилятор сворачивать - он покраснеет, и находку трека придётся
/// пересчитать. Это правильно; утверждение об окружении обязано пересчитываться
/// вместе с окружением.
#[test]
fn the_c_compiler_folds_the_foreign_call() {
    let machine = by_machine();
    let folded = in_c("outward-c-literal", IN_C_LITERAL, &[]);
    assert_ne!(
        folded, machine,
        "компилятор перестал сворачивать `cbrt`: находку трека C пора пересчитать"
    );
}

/// `-fno-builtin` возвращает согласие: лекарство названо и проверено.
///
/// Цена его не нулевая и здесь не мерится: ключ снимает у компилятора знание о
/// **всех** функциях стандартной библиотеки, то есть и о `memcpy` с `strlen`,
/// которыми порождённый код пользуется. Поэтому рядом проверяется и точечный
/// `-fno-builtin-cbrt`: он работает так же и стоил бы имени на каждый чужой
/// символ - то есть выбор между ними есть выбор цены, а не работоспособности.
#[test]
fn no_builtin_makes_the_c_side_agree_again() {
    let machine = by_machine();
    for (stem, flag) in [
        ("outward-c-nofold", "-fno-builtin"),
        ("outward-c-nofold-one", "-fno-builtin-cbrt"),
    ] {
        let called = in_c(stem, IN_C_LITERAL, &[flag]);
        assert_eq!(
            called, machine,
            "`{flag}` не вернул согласия: лекарство названо неверно"
        );
    }
}

/// LLVM на том же месте не сворачивает ничего.
///
/// Вторая половина находки, и без неё первая читалась бы как «литералы вообще
/// опасны». Опасны они **неодинаково**: конвейер `llvm-as`/`opt -O2`/`llc -O2`
/// оставляет `call double @cbrt(double 2.700000e+01)` вызовом, и ответ приходит
/// из той же glibc, что у машины. То есть расходятся между собой именно два
/// понижения, а машина стоит на стороне LLVM.
#[test]
fn the_llvm_pipeline_does_not_fold_the_foreign_call() {
    let Some(tools) = toolchain() else {
        return;
    };
    let machine = by_machine();
    let literal = in_llvm(&tools, "outward-ll-literal", IN_LLVM_LITERAL);
    assert_eq!(
        literal, machine,
        "LLVM начал сворачивать `cbrt`: находку трека C пора пересчитать"
    );
}
