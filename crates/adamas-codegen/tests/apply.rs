//! Применение замыкания в чистом отрезке: корень трамплина свой (трек A волны
//! 3 Фазы 7).
//!
//! Тринадцать программ корпуса LLVM-путь не брал отказом «применение замыкания
//! в чистом отрезке». План волны назвал средством **селекцию по целям
//! замыканий** - следующую ступень вопроса 74. Взята не она, и разошлось это с
//! постановкой замером: селекции здесь не нужно вовсе.
//!
//! # Почему селекции не нужно
//!
//! Какая из двух форм лежит за указателем, решает **трамплин замыкания**
//! (`box_N`, `emit_llvm::boxer`), и решает статически: номер функции ему
//! известен в момент печати, а `adamas_apply` зовёт его через поле объекта.
//! Место вызова про цель не знает и знать не обязано; чего ему недоставало -
//! **ручки стека**, потому что за указателем может оказаться дроблёное тело, и
//! кадр ему некуда положить.
//!
//! Ручка эта стоит `alloca ptr` (`adamas_kont` есть одна вершина) - и вот
//! утверждение, которое здесь считается числом: **кадра в куче чистый отрезок
//! не платит**.
//!
//! # Что здесь проверяется
//!
//! - *Чистая функция применяет и не кладёт кадра*
//!   ([`a_pure_segment_applies_without_a_heap_frame`]): в теле есть корень,
//!   `adamas_apply` и `adamas_kont_run`, и нет `adamas_kont_push` - точки
//!   входа, которой кадр выдаётся.
//! - *Вторая форма не расползлась* ([`the_second_form_does_not_spread`]): то же
//!   утверждение по **всему** корпусу разом - ни один чистый отрезок не кладёт
//!   кадра. Мера у вопроса 169 была «экземпляров у имени не больше двух»; здесь
//!   она другая, потому что формы эмиттер не раздаёт вовсе, а только читает:
//!   **ноль кадров в первой форме** при 92 применениях в ней.
//! - *Блоков выдано столько же, сколько у C-бэкенда*
//!   ([`the_unblocked_issue_the_blocks_the_c_backend_issues`]) - то же
//!   утверждение прогоном. Свидетель этот **не** дублирует корпусный договор:
//!   тот сверяет ответ и **живые** блоки, а выданные не сверяет никто, и
//!   мутант, добавляющий блок на применение, проходит его целиком.
//! - *Форма за указателем, не совпавшая с ожиданием места вызова, роняет
//!   прогон наблюдаемо* ([`a_second_form_behind_the_pointer_fails_loudly`]).
//!   Это то самое место, где «тихо неверный ответ» был бы худшим исходом, и
//!   вход сюда собирается **руками**: понижение такой пары не порождает -
//!   спрос места вызова (вопрос 169) заводит второй экземпляр раньше, - и
//!   предъявить её иначе нечем.

mod harness;

use adamas_codegen::ir::{
    Binding, Constructor, CtorId, Expr, Fact, Form, FuncId, Function, Label, LabelId, LocalId,
    Program, Repr,
};
use adamas_codegen::llvm::Pipeline;
use adamas_core::mult::Mult;

/// Чистая функция, применяющая значение: `forEach` без единой метки в типе.
///
/// Лямбда получает вторую форму **всегда** (`ir::Form`), значит за указателем
/// здесь именно она - и всё же кадра не кладётся ни одного: тело её ничем не
/// приостанавливается, и трамплин `box_N` зовёт его напрямую.
const PURE_APPLY: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

forEach : (ω f : a -> Unit) -> List a -> Unit
forEach f Nil = MkUnit
forEach f (Cons x xs) =
  let 1 u : Unit = f x
  forEach f xs

length : List a -> Nat
length Nil = Zero
length (Cons x xs) = Succ (length xs)

digits : List Nat
digits = Cons (Succ Zero) (Cons (Succ (Succ Zero)) Nil)

main : Nat
main =
  let 1 u : Unit = forEach (\\n -> MkUnit) digits
  length digits
";

/// Тело функции из текста `.ll` по её номеру.
///
/// Ищется **определение**, а не имя: место вызова пишет то же `@fn_N(`, и поиск
/// по имени однажды уже отдал чужое тело.
fn body(text: &str, number: usize) -> String {
    let head = format!("@fn_{number}(");
    let at = text
        .lines()
        .position(|line| line.starts_with("define") && line.contains(&head))
        .unwrap_or_else(|| panic!("определения `fn_{number}` в тексте нет:\n{text}"));
    text.lines()
        .skip(at)
        .take_while(|line| *line != "}")
        .collect::<Vec<_>>()
        .join("\n")
}

/// Чистый отрезок применяет значение и кадра в куче за это не платит.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
#[test]
fn a_pure_segment_applies_without_a_heap_frame() {
    let program = harness::llvm_program("pure-apply", PURE_APPLY).unwrap();
    let applying: Vec<&Function> = program
        .functions
        .iter()
        .filter(|function| {
            let mut found = false;
            harness::walk(&function.body, &mut |expr| {
                found |= matches!(expr, Expr::Apply { .. });
            });
            found
        })
        .collect();
    assert_eq!(
        applying.len(),
        1,
        "применение ожидалось одно: {:?}",
        applying.iter().map(|it| &it.name).collect::<Vec<_>>()
    );
    let applying = applying[0];
    assert_eq!(
        applying.form,
        Form::Stack,
        "`{}` применяет значение из второй формы: свидетель смотрит не туда",
        applying.name
    );
    let number = applying.id.0;

    let artefacts = harness::llvm_text("pure-apply", PURE_APPLY).unwrap();
    let text = body(&artefacts.ll, number);
    for expected in [
        "= alloca ptr",
        "call void @adamas_kont_init",
        "call ptr @adamas_apply",
        "call ptr @adamas_kont_run",
    ] {
        assert!(
            text.contains(expected),
            "в чистом отрезке нет `{expected}`:\n{text}"
        );
    }
    // Ради этой строки всё и затевалось: кадр выдаёт `adamas_kont_push`, и в
    // первой форме его нет ни одного. Появись он - приостановка стала бы
    // стоить блока кучи на каждое применение, то есть ровно то, чем платит
    // вторая форма (трек G волны 2).
    assert!(
        !text.contains("@adamas_kont_push"),
        "чистый отрезок кладёт кадр в кучу:\n{text}"
    );
}

/// Вторая форма не расползлась: **ни один** чистый отрезок корпуса не кладёт
/// кадра.
///
/// Мера у вопроса 169 была «экземпляров у имени не больше двух»; здесь она
/// другая и считается по всему корпусу разом: кадр выдаётся точкой входа
/// `adamas_kont_push`, и в теле функции **первой формы** его нет ни одного.
/// Маршрут, которого план ждал - отдать применяющей функции вторую форму, -
/// дал бы по кадру на применение, и эта строка стала бы красной.
///
/// Числа печатаются, но не закрепляются: корпус растят соседние треки, и
/// закреплённая сумма ломала бы их слияние, ничего при этом не утверждая.
/// Закреплено то, что от размера корпуса не зависит: кадров в первой форме
/// ноль, а применений в ней больше нуля - иначе свидетель зелен по пустоте.
/// Снятые прогоном 2026-09-16 значения: 88 программ, 739 функций второй формы,
/// 92 применения в первой.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
#[test]
fn the_second_form_does_not_spread() {
    let mut detached = 0usize;
    let mut pure_applications = 0usize;
    let mut framed_pure: Vec<String> = Vec::new();
    let mut framed_second = 0usize;
    let mut programs = 0usize;
    let mut fixtures: Vec<std::path::PathBuf> = std::fs::read_dir(harness::corpus())
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    fixtures.sort();
    for path in &fixtures {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let source = std::fs::read_to_string(path).unwrap();
        let Ok(artefacts) = harness::llvm_text(&name, &source) else {
            continue;
        };
        let program = harness::llvm_program(&name, &source).unwrap();
        programs += 1;
        // Положительный контроль: кадры в корпусе есть, и ищет их **та же**
        // строка. Без него «ноль кадров в первой форме» зеленело бы и от
        // опечатки в имени точки входа.
        framed_second += artefacts.ll.matches("@adamas_kont_push").count();
        for function in &program.functions {
            if function.form == Form::Detached {
                detached += 1;
                continue;
            }
            harness::walk(&function.body, &mut |expr| {
                if matches!(expr, Expr::Apply { .. }) {
                    pure_applications += 1;
                }
            });
            if body(&artefacts.ll, function.id.0).contains("@adamas_kont_push") {
                framed_pure.push(format!("{name}: `{}`", function.name));
            }
        }
    }
    eprintln!(
        "корпус LLVM-пути: программ {programs}, функций второй формы {detached}, \
         применений в первой форме {pure_applications}, кадров во второй {framed_second}"
    );
    assert!(
        pure_applications > 0,
        "применений в первой форме нет: считать нечего"
    );
    assert!(
        framed_second > 0,
        "кадров нет нигде: строка ищет не то, и ноль в первой форме ничего не значит"
    );
    assert!(
        framed_pure.is_empty(),
        "первая форма кладёт кадр в кучу: {framed_pure:?}"
    );
}

/// Тринадцать снятых программ: корень трамплина кучи не стоит.
///
/// Утверждение статическое ([`a_pure_segment_applies_without_a_heap_frame`])
/// подтверждается здесь **прогоном**: блоков выдано ровно столько же, сколько
/// выдаёт C-бэкенд на тех же исходниках. Кадр стоил бы блока на применение, и
/// расхождение было бы видно числом, а не текстом.
///
/// Тринадцать, а не восемьдесят восемь: у прочих применения в чистом отрезке
/// нет, и они мерили бы объектный слой, а не этот трек.
const UNBLOCKED: [&str; 13] = [
    "alias-computation",
    "beta-redex",
    "class-multiplicity",
    "classes",
    "decidable",
    "existential",
    "fibers",
    "functor",
    "interpreter",
    "operation-lambda",
    "operation-value",
    "prelude",
    "state",
];

/// Блоков выдано столько же, сколько у C-бэкенда: корень стоит на стеке.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_unblocked_issue_the_blocks_the_c_backend_issues() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let mut total = 0usize;
    for name in UNBLOCKED {
        let source =
            std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap();
        let artefacts = harness::llvm_text(name, &source).unwrap();
        let through_llvm = harness::llvm_printed(
            &format!("{name}.blocks"),
            &artefacts.ll,
            &artefacts.support,
            &tools,
            &pipeline,
        );
        let through_c = harness::c_printed(&format!("{name}.blocks-c"), &source);
        assert_eq!(
            through_llvm.allocated, through_c.allocated,
            "{name}: блоков выдано LLVM {:?} против {:?} у C",
            through_llvm.allocated, through_c.allocated
        );
        assert_eq!(through_llvm.live, Some(0), "{name}: блоки остались живыми");
        total += through_llvm.allocated.unwrap_or_default();
    }
    eprintln!("тринадцать снятых: блоков выдано {total}, столько же у C-бэкенда");
    assert!(total > 0, "блоков не выдано вовсе: считать нечего");
}

/// Вторая форма за указателем, которой место вызова не ждало, роняет прогон.
///
/// Вход собран руками, и это единственный способ: понижение такой пары не
/// порождает - спрос места вызова (вопрос 169) заводит второй экземпляр
/// окружающей раньше, чем метка доедет до применения. Свидетель поэтому стоит
/// на входе эмиттера.
///
/// Наблюдаемое - **обрыв с причиной**, а не ответ: вектора evidence у первой
/// формы нет, `adamas_evidence_lookup` на `NULL` отвечает `MISSING`, и печать
/// до ответа не доходит. Ровно то, чего требует правило трека: неверное
/// ожидание обязано падать наблюдаемо, а не отвечать тихо.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn a_second_form_behind_the_pointer_fails_loudly() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let produces = Function {
        id: FuncId(1),
        name: "производящая".to_owned(),
        position: None,
        form: Form::Detached,
        captured: Vec::new(),
        parameters: vec![Binding {
            name: "x".to_owned(),
            local: LocalId(0),
            fact: Fact::present(Mult::Many),
        }],
        result: Repr::Boxed,
        body: Expr::Perform {
            label: LabelId(0),
            operation: 0,
            arguments: Vec::new(),
        },
    };
    let entry = Function {
        id: FuncId(0),
        name: "main".to_owned(),
        position: None,
        form: Form::Stack,
        captured: Vec::new(),
        parameters: Vec::new(),
        result: Repr::Boxed,
        body: Expr::Apply {
            callee: Box::new(Expr::Closure {
                function: FuncId(1),
                captured: Vec::new(),
            }),
            argument: Box::new(Expr::Construct {
                constructor: CtorId(0),
                reuse: None,
                arguments: Vec::new(),
            }),
        },
    };
    let program = Program {
        constructors: vec![Constructor {
            tag: CtorId(0),
            name: "MkUnit".to_owned(),
            data: "Unit".to_owned(),
            binders: Vec::new(),
            params: 0,
            labels: None,
        }],
        packings: Vec::new(),
        labels: vec![Label {
            name: "Ask".to_owned(),
            operations: vec!["ask".to_owned()],
        }],
        handlers: Vec::new(),
        functions: vec![entry, produces],
        entry: FuncId(0),
        source: None,
    };
    let artefacts = adamas_codegen::emit_llvm::emit(&program)
        .expect("эмиссия обязана пройти: отказа тут нет, дефект живёт в прогоне");
    let outcome = harness::llvm_printed(
        "apply-mismatch",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &Pipeline::optimised(),
    );
    assert_eq!(
        outcome.printed, "прогон оборвался",
        "форма за указателем не совпала, а прогон ответил: {}",
        outcome.printed
    );
    assert!(
        outcome.reason.contains("операция без хендлера"),
        "обрыв не назвал причины: {}",
        outcome.reason
    );
}
